import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation16061_implies_Equation2 (G : Type*) [Magma G] (h : Equation16061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16062_implies_Equation2 (G : Type*) [Magma G] (h : Equation16062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation16063_implies_Equation2 (G : Type*) [Magma G] (h : Equation16063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X7) ◇ (((X4 ◇ (X5 ◇ X6)) ◇ X0) ◇ X6))) = X7 := superpose eq7 eq7
  have eq13 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16064_implies_Equation2 (G : Type*) [Magma G] (h : Equation16064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X0) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16066_implies_Equation2 (G : Type*) [Magma G] (h : Equation16066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16067_implies_Equation2 (G : Type*) [Magma G] (h : Equation16067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16068_implies_Equation2 (G : Type*) [Magma G] (h : Equation16068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16069_implies_Equation2 (G : Type*) [Magma G] (h : Equation16069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16070_implies_Equation2 (G : Type*) [Magma G] (h : Equation16070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16072_implies_Equation2 (G : Type*) [Magma G] (h : Equation16072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16073_implies_Equation2 (G : Type*) [Magma G] (h : Equation16073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16074_implies_Equation2 (G : Type*) [Magma G] (h : Equation16074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16075_implies_Equation2 (G : Type*) [Magma G] (h : Equation16075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16076_implies_Equation2 (G : Type*) [Magma G] (h : Equation16076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X2) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16078_implies_Equation2 (G : Type*) [Magma G] (h : Equation16078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16079_implies_Equation2 (G : Type*) [Magma G] (h : Equation16079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16080_implies_Equation2 (G : Type*) [Magma G] (h : Equation16080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16081_implies_Equation2 (G : Type*) [Magma G] (h : Equation16081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16082_implies_Equation2 (G : Type*) [Magma G] (h : Equation16082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X3) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16084_implies_Equation2 (G : Type*) [Magma G] (h : Equation16084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16085_implies_Equation2 (G : Type*) [Magma G] (h : Equation16085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16086_implies_Equation2 (G : Type*) [Magma G] (h : Equation16086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16087_implies_Equation2 (G : Type*) [Magma G] (h : Equation16087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16088_implies_Equation2 (G : Type*) [Magma G] (h : Equation16088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16090_implies_Equation2 (G : Type*) [Magma G] (h : Equation16090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X5) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16091_implies_Equation2 (G : Type*) [Magma G] (h : Equation16091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X5) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16092_implies_Equation2 (G : Type*) [Magma G] (h : Equation16092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X5) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16093_implies_Equation2 (G : Type*) [Magma G] (h : Equation16093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X5) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16094_implies_Equation2 (G : Type*) [Magma G] (h : Equation16094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X5) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16095_implies_Equation2 (G : Type*) [Magma G] (h : Equation16095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X5) ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16301_implies_Equation2 (G : Type*) [Magma G] (h : Equation16301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq66 eq15


@[equational_result]
theorem Equation16304_implies_Equation2 (G : Type*) [Magma G] (h : Equation16304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq47 eq11


@[equational_result]
theorem Equation16306_implies_Equation2 (G : Type*) [Magma G] (h : Equation16306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq39 eq14


@[equational_result]
theorem Equation16307_implies_Equation2 (G : Type*) [Magma G] (h : Equation16307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation16308_implies_Equation2 (G : Type*) [Magma G] (h : Equation16308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16311_implies_Equation2 (G : Type*) [Magma G] (h : Equation16311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation16314_implies_Equation2 (G : Type*) [Magma G] (h : Equation16314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation16316_implies_Equation2 (G : Type*) [Magma G] (h : Equation16316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16318_implies_Equation2 (G : Type*) [Magma G] (h : Equation16318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation16320_implies_Equation2 (G : Type*) [Magma G] (h : Equation16320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (((X2 ◇ X2) ◇ X3) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq9
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq26
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq117 eq32


@[equational_result]
theorem Equation16321_implies_Equation2 (G : Type*) [Magma G] (h : Equation16321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((((X0 ◇ X0) ◇ X3) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq66 eq15


@[equational_result]
theorem Equation16322_implies_Equation2 (G : Type*) [Magma G] (h : Equation16322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation16324_implies_Equation2 (G : Type*) [Magma G] (h : Equation16324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation16326_implies_Equation2 (G : Type*) [Magma G] (h : Equation16326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation16329_implies_Equation2 (G : Type*) [Magma G] (h : Equation16329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((((X0 ◇ X0) ◇ X3) ◇ X3) ◇ X3)) ◇ ((((X0 ◇ X0) ◇ X3) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq75 eq14


@[equational_result]
theorem Equation16330_implies_Equation2 (G : Type*) [Magma G] (h : Equation16330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16332_implies_Equation2 (G : Type*) [Magma G] (h : Equation16332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation16333_implies_Equation2 (G : Type*) [Magma G] (h : Equation16333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ ((((X0 ◇ X0) ◇ X3) ◇ X4) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation16334_implies_Equation2 (G : Type*) [Magma G] (h : Equation16334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X4) ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation16335_implies_Equation2 (G : Type*) [Magma G] (h : Equation16335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16338_implies_Equation2 (G : Type*) [Magma G] (h : Equation16338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq48 eq11


@[equational_result]
theorem Equation16341_implies_Equation2 (G : Type*) [Magma G] (h : Equation16341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq45 eq11


@[equational_result]
theorem Equation16343_implies_Equation2 (G : Type*) [Magma G] (h : Equation16343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation16345_implies_Equation2 (G : Type*) [Magma G] (h : Equation16345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation16348_implies_Equation2 (G : Type*) [Magma G] (h : Equation16348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq48 eq11


@[equational_result]
theorem Equation16351_implies_Equation2 (G : Type*) [Magma G] (h : Equation16351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq49 eq11


@[equational_result]
theorem Equation16353_implies_Equation2 (G : Type*) [Magma G] (h : Equation16353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq48 eq14


@[equational_result]
theorem Equation16354_implies_Equation2 (G : Type*) [Magma G] (h : Equation16354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (((X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq10
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq7 eq16
  have eq52 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq37 eq7
  have eq53 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3)) = X1 := superpose eq37 eq9
  have eq77 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq37 eq52
  have eq79 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X3) = X1 := superpose eq77 eq53
  have eq80 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq77 eq79
  have eq96 (X0 X1 : G) : X0 = X1 := superpose eq77 eq80
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq98 eq96


@[equational_result]
theorem Equation16355_implies_Equation2 (G : Type*) [Magma G] (h : Equation16355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation16357_implies_Equation2 (G : Type*) [Magma G] (h : Equation16357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1) ◇ (((X0 ◇ X3) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X1)) ◇ X5) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq12 eq12
  have eq39 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq12
  have eq48 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq12
  have eq80 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq39 eq37
  have eq82 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq48 eq80
  have eq87 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X0 := superpose eq82 eq7
  have eq101 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq82 eq87
  have eq147 (X0 X2 : G) : X0 = X2 := superpose eq101 eq101
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq147 eq8
  subsumption eq149 eq147


@[equational_result]
theorem Equation16359_implies_Equation2 (G : Type*) [Magma G] (h : Equation16359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq40 eq12


@[equational_result]
theorem Equation16361_implies_Equation2 (G : Type*) [Magma G] (h : Equation16361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation16362_implies_Equation2 (G : Type*) [Magma G] (h : Equation16362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X2 ◇ X1)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ (X0 ◇ ((((X1 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2))) ◇ X4) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2))) ◇ X4))) = X3 := superpose eq7 eq10
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ ((((X1 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2))) ◇ X4) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2))) ◇ X4)) = X3 := superpose eq19 eq11
  have eq33 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ X4) = X3 := superpose eq19 eq22
  have eq34 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq19 eq33
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq40 eq35


@[equational_result]
theorem Equation16363_implies_Equation2 (G : Type*) [Magma G] (h : Equation16363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation16365_implies_Equation2 (G : Type*) [Magma G] (h : Equation16365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((((X0 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) ◇ (X2 ◇ X1))) ◇ X1)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq10
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq7 eq17
  have eq53 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq39 eq7
  have eq79 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq39 eq53
  have eq80 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq79 eq39
  have eq119 (X0 X1 : G) : X0 = X1 := superpose eq79 eq80
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq124 eq119


@[equational_result]
theorem Equation16367_implies_Equation2 (G : Type*) [Magma G] (h : Equation16367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation16369_implies_Equation2 (G : Type*) [Magma G] (h : Equation16369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation16370_implies_Equation2 (G : Type*) [Magma G] (h : Equation16370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq62 eq15


@[equational_result]
theorem Equation16371_implies_Equation2 (G : Type*) [Magma G] (h : Equation16371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X5)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq65 eq17


@[equational_result]
theorem Equation16372_implies_Equation2 (G : Type*) [Magma G] (h : Equation16372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16374_implies_Equation2 (G : Type*) [Magma G] (h : Equation16374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq10 eq9
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq26
  have eq88 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq181 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq181 eq88


@[equational_result]
theorem Equation16375_implies_Equation2 (G : Type*) [Magma G] (h : Equation16375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ ((((X0 ◇ X3) ◇ X0) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16376_implies_Equation2 (G : Type*) [Magma G] (h : Equation16376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16378_implies_Equation2 (G : Type*) [Magma G] (h : Equation16378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X2 ◇ X3) ◇ X2)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ X0) ◇ X2) ◇ X2) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : (((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq7 eq10
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X3 ◇ X1)) ◇ X5) ◇ X5) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq12 eq12
  have eq37 (X0 X2 X3 X4 : G) : (((X3 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X4) ◇ X4) = X0 := superpose eq7 eq12
  have eq38 (X0 X2 X3 X4 : G) : (((X3 ◇ (X2 ◇ X0)) ◇ X4) ◇ X4) = X0 := superpose eq9 eq12
  have eq75 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq37 eq25
  have eq76 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq38 eq36
  have eq88 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq75
  have eq113 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq88 eq76
  have eq117 (X0 X3 : G) : X0 = X3 := superpose eq7 eq113
  have eq264 (X0 : G) : sK0 ≠ X0 := superpose eq117 eq8
  subsumption eq264 eq117


@[equational_result]
theorem Equation16380_implies_Equation2 (G : Type*) [Magma G] (h : Equation16380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation16382_implies_Equation2 (G : Type*) [Magma G] (h : Equation16382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ ((((X0 ◇ X3) ◇ X0) ◇ X3) ◇ X2)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X2 ◇ X3) ◇ X2) ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X3) ◇ X0) ◇ X3) ◇ (((X2 ◇ X4) ◇ X2) ◇ X4)) = (X1 ◇ (((X2 ◇ ((((X0 ◇ X3) ◇ X0) ◇ X3) ◇ (((X2 ◇ X4) ◇ X2) ◇ X4))) ◇ X0) ◇ X1)) := superpose eq7 eq9
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ (((X0 ◇ X4) ◇ X0) ◇ X4)) ◇ X5) ◇ (((X0 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ (((X0 ◇ X4) ◇ X0) ◇ X4))) ◇ X2) ◇ X5)) ◇ X1)) = X5 := superpose eq10 eq9
  have eq1071 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (((X0 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ (((X0 ◇ X4) ◇ X0) ◇ X4))) ◇ X2) ◇ X2)) ◇ X1)) = X2 := superpose eq10 eq27
  have eq1203 (X0 X1 X2 X3 : G) : (X3 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ X3)) = X0 := superpose eq15 eq1071
  have eq1390 (X0 X1 X2 X3 X4 X5 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ ((((X3 ◇ X4) ◇ X3) ◇ X4) ◇ (((X3 ◇ X5) ◇ X3) ◇ X5))) ◇ X0) = X3 := superpose eq1203 eq1203
  have eq1398 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq1203
  have eq1588 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ X1)) = X2 := superpose eq1398 eq9
  have eq1688 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1)) = X2 := superpose eq1398 eq1588
  have eq1689 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1)) = X2 := superpose eq1398 eq1688
  have eq1690 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq1398 eq1689
  have eq1715 (X0 X2 X3 X4 : G) : ((((X0 ◇ X3) ◇ X0) ◇ X3) ◇ (((X2 ◇ X4) ◇ X2) ◇ X4)) = X0 := superpose eq1690 eq15
  have eq2232 (X0 X3 X4 X5 : G) : ((X0 ◇ ((((X3 ◇ X4) ◇ X3) ◇ X4) ◇ (((X3 ◇ X5) ◇ X3) ◇ X5))) ◇ X0) = X3 := superpose eq1715 eq1390
  have eq2283 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X3 := superpose eq1715 eq2232
  have eq2377 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := superpose eq2283 eq7
  have eq3068 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq1398 eq2377
  have eq3290 (X0 X3 : G) : X0 = X3 := superpose eq3068 eq3068
  have eq3293 (X0 : G) : sK0 ≠ X0 := superpose eq3290 eq8
  subsumption eq3293 eq3290


@[equational_result]
theorem Equation16383_implies_Equation2 (G : Type*) [Magma G] (h : Equation16383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ ((((X0 ◇ X3) ◇ X0) ◇ X3) ◇ X3)) ◇ ((((X0 ◇ X3) ◇ X0) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16384_implies_Equation2 (G : Type*) [Magma G] (h : Equation16384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16386_implies_Equation2 (G : Type*) [Magma G] (h : Equation16386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation16387_implies_Equation2 (G : Type*) [Magma G] (h : Equation16387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X5) ◇ ((((X0 ◇ X3) ◇ X0) ◇ X4) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16388_implies_Equation2 (G : Type*) [Magma G] (h : Equation16388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X4) ◇ X0) ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16389_implies_Equation2 (G : Type*) [Magma G] (h : Equation16389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16391_implies_Equation2 (G : Type*) [Magma G] (h : Equation16391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X2) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X3) ◇ (X2 ◇ X1)) ◇ X0) ◇ (X2 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X2 ◇ X1)) := superpose eq9 eq9
  have eq17 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3)))) = X2 := superpose eq13 eq10
  have eq64 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq14 eq7
  have eq65 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq14 eq9
  have eq97 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq65 eq65
  have eq118 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X0) := superpose eq97 eq64
  have eq173 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := superpose eq17 eq118
  have eq175 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq65 eq118
  have eq261 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq175 eq173
  have eq327 (X0 X3 : G) : X0 = X3 := superpose eq7 eq261
  have eq473 (X0 : G) : sK0 ≠ X0 := superpose eq327 eq8
  subsumption eq473 eq327


@[equational_result]
theorem Equation16393_implies_Equation2 (G : Type*) [Magma G] (h : Equation16393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation16395_implies_Equation2 (G : Type*) [Magma G] (h : Equation16395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation16397_implies_Equation2 (G : Type*) [Magma G] (h : Equation16397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation16399_implies_Equation2 (G : Type*) [Magma G] (h : Equation16399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ ((((X0 ◇ X3) ◇ X2) ◇ X3) ◇ X2)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq42 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) = X0 := superpose eq7 eq17
  have eq59 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq42 eq7
  have eq88 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X2) = X0 := superpose eq59 eq42
  have eq89 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq59 eq88
  have eq90 (X0 X3 : G) : X0 = X3 := superpose eq89 eq89
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq95 eq90


@[equational_result]
theorem Equation16401_implies_Equation2 (G : Type*) [Magma G] (h : Equation16401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation16403_implies_Equation2 (G : Type*) [Magma G] (h : Equation16403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq57 eq15


@[equational_result]
theorem Equation16404_implies_Equation2 (G : Type*) [Magma G] (h : Equation16404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation16405_implies_Equation2 (G : Type*) [Magma G] (h : Equation16405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X5) ◇ X5)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation16406_implies_Equation2 (G : Type*) [Magma G] (h : Equation16406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16409_implies_Equation2 (G : Type*) [Magma G] (h : Equation16409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ ((((X0 ◇ X3) ◇ X3) ◇ X0) ◇ X3)) ◇ X2) ◇ ((((X0 ◇ X3) ◇ X3) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16410_implies_Equation2 (G : Type*) [Magma G] (h : Equation16410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation16412_implies_Equation2 (G : Type*) [Magma G] (h : Equation16412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ ((((X0 ◇ X3) ◇ X3) ◇ X2) ◇ X2)) ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq9
  have eq37 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq7 eq15
  have eq60 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq37 eq7
  have eq84 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq37 eq60
  have eq85 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq84 eq37
  have eq116 (X0 X1 : G) : X0 = X1 := superpose eq84 eq85
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq116 eq8
  subsumption eq130 eq116


@[equational_result]
theorem Equation16414_implies_Equation2 (G : Type*) [Magma G] (h : Equation16414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation16417_implies_Equation2 (G : Type*) [Magma G] (h : Equation16417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ ((((X0 ◇ X3) ◇ X3) ◇ X3) ◇ X3)) ◇ ((((X0 ◇ X3) ◇ X3) ◇ X3) ◇ X3)) ◇ ((((X0 ◇ X3) ◇ X3) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16418_implies_Equation2 (G : Type*) [Magma G] (h : Equation16418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16420_implies_Equation2 (G : Type*) [Magma G] (h : Equation16420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq58 eq15


@[equational_result]
theorem Equation16421_implies_Equation2 (G : Type*) [Magma G] (h : Equation16421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ ((((X0 ◇ X3) ◇ X3) ◇ X4) ◇ X3)) ◇ X5) ◇ ((((X0 ◇ X3) ◇ X3) ◇ X4) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16422_implies_Equation2 (G : Type*) [Magma G] (h : Equation16422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X4) ◇ X4) ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation16423_implies_Equation2 (G : Type*) [Magma G] (h : Equation16423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16425_implies_Equation2 (G : Type*) [Magma G] (h : Equation16425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (((X3 ◇ X4) ◇ X5) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X1)) ◇ X5) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq13 eq13
  have eq40 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq13
  have eq76 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq40 eq37
  have eq102 (X0 X1 X2 X3 X4 X5 : G) : (((((X2 ◇ X3) ◇ X4) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X5 := superpose eq13 eq11
  have eq119 (X1 X2 X5 : G) : (X1 ◇ X2) = X5 := superpose eq76 eq102
  have eq120 (X0 X6 : G) : X0 = X6 := superpose eq11 eq119
  have eq226 (X0 : G) : sK0 ≠ X0 := superpose eq120 eq8
  subsumption eq226 eq120


@[equational_result]
theorem Equation16426_implies_Equation2 (G : Type*) [Magma G] (h : Equation16426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X2) ◇ ((((X0 ◇ X3) ◇ X4) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16427_implies_Equation2 (G : Type*) [Magma G] (h : Equation16427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((((X0 ◇ X4) ◇ X5) ◇ X0) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16428_implies_Equation2 (G : Type*) [Magma G] (h : Equation16428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16430_implies_Equation2 (G : Type*) [Magma G] (h : Equation16430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation16431_implies_Equation2 (G : Type*) [Magma G] (h : Equation16431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X3)) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation16432_implies_Equation2 (G : Type*) [Magma G] (h : Equation16432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X1) ◇ X5)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation16433_implies_Equation2 (G : Type*) [Magma G] (h : Equation16433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation16435_implies_Equation2 (G : Type*) [Magma G] (h : Equation16435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation16436_implies_Equation2 (G : Type*) [Magma G] (h : Equation16436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ ((((X0 ◇ X3) ◇ X4) ◇ X3) ◇ X3)) ◇ ((((X0 ◇ X3) ◇ X4) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16437_implies_Equation2 (G : Type*) [Magma G] (h : Equation16437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16438_implies_Equation2 (G : Type*) [Magma G] (h : Equation16438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16440_implies_Equation2 (G : Type*) [Magma G] (h : Equation16440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X5) ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation16441_implies_Equation2 (G : Type*) [Magma G] (h : Equation16441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X5) ◇ ((((X0 ◇ X3) ◇ X4) ◇ X4) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16442_implies_Equation2 (G : Type*) [Magma G] (h : Equation16442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X0 ◇ ((((X0 ◇ X4) ◇ X5) ◇ X5) ◇ X5)) ◇ ((((X0 ◇ X4) ◇ X5) ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation16443_implies_Equation2 (G : Type*) [Magma G] (h : Equation16443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16445_implies_Equation2 (G : Type*) [Magma G] (h : Equation16445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation16446_implies_Equation2 (G : Type*) [Magma G] (h : Equation16446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ (((X0 ◇ X6) ◇ X7) ◇ ((((X0 ◇ X3) ◇ X4) ◇ X5) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16447_implies_Equation2 (G : Type*) [Magma G] (h : Equation16447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ ((X0 ◇ X7) ◇ ((((X0 ◇ X4) ◇ X5) ◇ X6) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation16448_implies_Equation2 (G : Type*) [Magma G] (h : Equation16448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 X6 X7 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ X7))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation16449_implies_Equation2 (G : Type*) [Magma G] (h : Equation16449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16452_implies_Equation2 (G : Type*) [Magma G] (h : Equation16452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation16455_implies_Equation2 (G : Type*) [Magma G] (h : Equation16455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation16457_implies_Equation2 (G : Type*) [Magma G] (h : Equation16457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16458_implies_Equation2 (G : Type*) [Magma G] (h : Equation16458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) = (X1 ◇ (((X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq7 eq10
  have eq26 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) = (X1 ◇ ((((((X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ X4) ◇ X4) ◇ (((X3 ◇ (((((X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ X4) ◇ X4)) ◇ X5) ◇ X5))) := superpose eq9 eq9
  have eq72 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3))) = X0 := superpose eq26 eq10
  have eq100 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3))) = X0 := superpose eq17 eq72
  have eq105 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) = X1 := superpose eq100 eq28
  have eq151 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq105 eq7
  have eq185 (X0 X2 : G) : X0 = X2 := superpose eq151 eq151
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq185 eq8
  subsumption eq187 eq185


@[equational_result]
theorem Equation16459_implies_Equation2 (G : Type*) [Magma G] (h : Equation16459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation16462_implies_Equation2 (G : Type*) [Magma G] (h : Equation16462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation16465_implies_Equation2 (G : Type*) [Magma G] (h : Equation16465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq66 eq11


@[equational_result]
theorem Equation16467_implies_Equation2 (G : Type*) [Magma G] (h : Equation16467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq63 eq14


@[equational_result]
theorem Equation16469_implies_Equation2 (G : Type*) [Magma G] (h : Equation16469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation16471_implies_Equation2 (G : Type*) [Magma G] (h : Equation16471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = (X1 ◇ (((X0 ◇ X3) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq39 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq12
  have eq80 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq39 eq9
  have eq85 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq80 eq7
  have eq90 (X0 X2 : G) : X0 = X2 := superpose eq10 eq85
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq109 eq90


@[equational_result]
theorem Equation16472_implies_Equation2 (G : Type*) [Magma G] (h : Equation16472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq122 eq38


@[equational_result]
theorem Equation16473_implies_Equation2 (G : Type*) [Magma G] (h : Equation16473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16475_implies_Equation2 (G : Type*) [Magma G] (h : Equation16475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq65 eq15


@[equational_result]
theorem Equation16477_implies_Equation2 (G : Type*) [Magma G] (h : Equation16477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation16481_implies_Equation2 (G : Type*) [Magma G] (h : Equation16481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq75 eq12


@[equational_result]
theorem Equation16483_implies_Equation2 (G : Type*) [Magma G] (h : Equation16483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation16484_implies_Equation2 (G : Type*) [Magma G] (h : Equation16484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq79 eq15


@[equational_result]
theorem Equation16485_implies_Equation2 (G : Type*) [Magma G] (h : Equation16485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X5)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq83 eq17


@[equational_result]
theorem Equation16486_implies_Equation2 (G : Type*) [Magma G] (h : Equation16486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16489_implies_Equation2 (G : Type*) [Magma G] (h : Equation16489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation16492_implies_Equation2 (G : Type*) [Magma G] (h : Equation16492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq65 eq11


@[equational_result]
theorem Equation16494_implies_Equation2 (G : Type*) [Magma G] (h : Equation16494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation16496_implies_Equation2 (G : Type*) [Magma G] (h : Equation16496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation16499_implies_Equation2 (G : Type*) [Magma G] (h : Equation16499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq63 eq11


@[equational_result]
theorem Equation16501_implies_Equation2 (G : Type*) [Magma G] (h : Equation16501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation16502_implies_Equation2 (G : Type*) [Magma G] (h : Equation16502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16504_implies_Equation2 (G : Type*) [Magma G] (h : Equation16504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16505_implies_Equation2 (G : Type*) [Magma G] (h : Equation16505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16506_implies_Equation2 (G : Type*) [Magma G] (h : Equation16506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16508_implies_Equation2 (G : Type*) [Magma G] (h : Equation16508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq9 eq9
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq10 eq10
  have eq26 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq7
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq10 eq7
  have eq31 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq9 eq20
  have eq39 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq9 eq12
  have eq80 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq39 eq31
  have eq81 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X2 := superpose eq39 eq28
  have eq84 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq80
  have eq87 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq84 eq26
  have eq91 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq84 eq81
  have eq92 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X0)) = X1 := superpose eq91 eq87
  have eq100 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = X1 := superpose eq91 eq92
  have eq101 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq91 eq100
  have eq102 (X0 X1 : G) : X0 = X1 := superpose eq84 eq101
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq110 eq102


@[equational_result]
theorem Equation16509_implies_Equation2 (G : Type*) [Magma G] (h : Equation16509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq9
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := superpose eq17 eq7
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq17 eq9
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq17 eq24
  have eq55 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X0 := superpose eq17 eq31
  have eq58 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq17 eq31
  have eq62 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq23 eq31
  have eq67 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq62 eq58
  have eq69 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq62 eq67
  have eq70 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := superpose eq69 eq55
  have eq87 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq69 eq70
  have eq88 (X0 X1 : G) : X0 = X1 := superpose eq17 eq87
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq96 eq88


@[equational_result]
theorem Equation16510_implies_Equation2 (G : Type*) [Magma G] (h : Equation16510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16512_implies_Equation2 (G : Type*) [Magma G] (h : Equation16512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16513_implies_Equation2 (G : Type*) [Magma G] (h : Equation16513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16514_implies_Equation2 (G : Type*) [Magma G] (h : Equation16514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16516_implies_Equation2 (G : Type*) [Magma G] (h : Equation16516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16517_implies_Equation2 (G : Type*) [Magma G] (h : Equation16517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16518_implies_Equation2 (G : Type*) [Magma G] (h : Equation16518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16520_implies_Equation2 (G : Type*) [Magma G] (h : Equation16520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16521_implies_Equation2 (G : Type*) [Magma G] (h : Equation16521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16522_implies_Equation2 (G : Type*) [Magma G] (h : Equation16522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16523_implies_Equation2 (G : Type*) [Magma G] (h : Equation16523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16525_implies_Equation2 (G : Type*) [Magma G] (h : Equation16525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (((X0 ◇ X3) ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) = (X1 ◇ ((X0 ◇ (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq10
  have eq44 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq14 eq14
  have eq55 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq14 eq9
  have eq57 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq55 eq26
  have eq70 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq57 eq7
  have eq117 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq70 eq44
  have eq145 (X0 X2 : G) : X0 = X2 := superpose eq117 eq55
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq145 eq8
  subsumption eq168 eq145


@[equational_result]
theorem Equation16527_implies_Equation2 (G : Type*) [Magma G] (h : Equation16527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation16529_implies_Equation2 (G : Type*) [Magma G] (h : Equation16529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (((X0 ◇ X3) ◇ X1) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = (X1 ◇ (((((X4 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1)) := superpose eq9 eq10
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq10 eq7
  have eq36 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1))) = X3 := superpose eq7 eq27
  have eq43 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq27 eq27
  have eq45 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) = X1 := superpose eq27 eq27
  have eq57 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq36 eq43
  have eq59 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq45 eq57
  have eq60 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = X1 := superpose eq59 eq22
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = X1 := superpose eq59 eq27
  have eq79 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq59 eq60
  have eq80 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq59 eq79
  have eq82 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq59 eq62
  have eq90 (X0 X1 : G) : X0 = X1 := superpose eq80 eq82
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq95 eq90


@[equational_result]
theorem Equation16531_implies_Equation2 (G : Type*) [Magma G] (h : Equation16531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation16535_implies_Equation2 (G : Type*) [Magma G] (h : Equation16535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation16537_implies_Equation2 (G : Type*) [Magma G] (h : Equation16537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation16538_implies_Equation2 (G : Type*) [Magma G] (h : Equation16538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation16539_implies_Equation2 (G : Type*) [Magma G] (h : Equation16539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (((X0 ◇ X4) ◇ X5) ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq11
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation16540_implies_Equation2 (G : Type*) [Magma G] (h : Equation16540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16542_implies_Equation2 (G : Type*) [Magma G] (h : Equation16542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq7
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq10 eq9
  have eq39 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1))))) = X2 := superpose eq26 eq26
  have eq49 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq26 eq9
  have eq57 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq49 eq29
  have eq68 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq26 eq57
  have eq104 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X2 := superpose eq68 eq39
  have eq106 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq49 eq104
  have eq107 (X0 X3 : G) : X0 = X3 := superpose eq7 eq106
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq207 eq107


@[equational_result]
theorem Equation16544_implies_Equation2 (G : Type*) [Magma G] (h : Equation16544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation16546_implies_Equation2 (G : Type*) [Magma G] (h : Equation16546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16547_implies_Equation2 (G : Type*) [Magma G] (h : Equation16547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16548_implies_Equation2 (G : Type*) [Magma G] (h : Equation16548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16550_implies_Equation2 (G : Type*) [Magma G] (h : Equation16550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16551_implies_Equation2 (G : Type*) [Magma G] (h : Equation16551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16552_implies_Equation2 (G : Type*) [Magma G] (h : Equation16552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16554_implies_Equation2 (G : Type*) [Magma G] (h : Equation16554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16555_implies_Equation2 (G : Type*) [Magma G] (h : Equation16555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16556_implies_Equation2 (G : Type*) [Magma G] (h : Equation16556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16557_implies_Equation2 (G : Type*) [Magma G] (h : Equation16557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16561_implies_Equation2 (G : Type*) [Magma G] (h : Equation16561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation16563_implies_Equation2 (G : Type*) [Magma G] (h : Equation16563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16564_implies_Equation2 (G : Type*) [Magma G] (h : Equation16564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16565_implies_Equation2 (G : Type*) [Magma G] (h : Equation16565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16567_implies_Equation2 (G : Type*) [Magma G] (h : Equation16567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16568_implies_Equation2 (G : Type*) [Magma G] (h : Equation16568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16569_implies_Equation2 (G : Type*) [Magma G] (h : Equation16569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16571_implies_Equation2 (G : Type*) [Magma G] (h : Equation16571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16572_implies_Equation2 (G : Type*) [Magma G] (h : Equation16572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16573_implies_Equation2 (G : Type*) [Magma G] (h : Equation16573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16574_implies_Equation2 (G : Type*) [Magma G] (h : Equation16574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16576_implies_Equation2 (G : Type*) [Magma G] (h : Equation16576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq48 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq13
  have eq129 (X0 X4 : G) : X0 = X4 := superpose eq7 eq48
  have eq227 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq227 eq129


@[equational_result]
theorem Equation16577_implies_Equation2 (G : Type*) [Magma G] (h : Equation16577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X4) ◇ X5) ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X2)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq10 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16578_implies_Equation2 (G : Type*) [Magma G] (h : Equation16578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (((X0 ◇ X4) ◇ X5) ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq9 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation16579_implies_Equation2 (G : Type*) [Magma G] (h : Equation16579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16581_implies_Equation2 (G : Type*) [Magma G] (h : Equation16581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16582_implies_Equation2 (G : Type*) [Magma G] (h : Equation16582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16583_implies_Equation2 (G : Type*) [Magma G] (h : Equation16583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16584_implies_Equation2 (G : Type*) [Magma G] (h : Equation16584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16586_implies_Equation2 (G : Type*) [Magma G] (h : Equation16586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16587_implies_Equation2 (G : Type*) [Magma G] (h : Equation16587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16588_implies_Equation2 (G : Type*) [Magma G] (h : Equation16588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16589_implies_Equation2 (G : Type*) [Magma G] (h : Equation16589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16591_implies_Equation2 (G : Type*) [Magma G] (h : Equation16591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16592_implies_Equation2 (G : Type*) [Magma G] (h : Equation16592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16593_implies_Equation2 (G : Type*) [Magma G] (h : Equation16593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16594_implies_Equation2 (G : Type*) [Magma G] (h : Equation16594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16596_implies_Equation2 (G : Type*) [Magma G] (h : Equation16596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16597_implies_Equation2 (G : Type*) [Magma G] (h : Equation16597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16598_implies_Equation2 (G : Type*) [Magma G] (h : Equation16598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16599_implies_Equation2 (G : Type*) [Magma G] (h : Equation16599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16600_implies_Equation2 (G : Type*) [Magma G] (h : Equation16600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16602_implies_Equation2 (G : Type*) [Magma G] (h : Equation16602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X3 ◇ X0) ◇ X0) ◇ X0) ◇ X2) = (X1 ◇ (((X0 ◇ ((((X3 ◇ X0) ◇ X0) ◇ X0) ◇ X2)) ◇ ((((X3 ◇ X0) ◇ X0) ◇ X0) ◇ X2)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq10 eq10
  have eq23 (X0 X1 X3 : G) : (X1 ◇ (((X0 ◇ X3) ◇ X3) ◇ X1)) = X3 := superpose eq10 eq7
  have eq48 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq10 eq19
  have eq66 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq10 eq23
  have eq72 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq23 eq23
  have eq85 (X0 X1 X2 X3 : G) : (((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ X3) = ((((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ X3) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ X3))) := superpose eq9 eq48
  have eq88 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq48 eq48
  have eq103 (X0 X1 X2 X3 : G) : (((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ X3) = X2 := superpose eq66 eq85
  have eq106 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((((X3 ◇ X0) ◇ X0) ◇ X0) ◇ X2) := superpose eq103 eq9
  have eq110 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq48 eq88
  have eq124 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3) = X2 := superpose eq110 eq103
  have eq125 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X3 ◇ X0) ◇ X0) ◇ X2) := superpose eq110 eq106
  have eq130 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq48 eq125
  have eq157 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq130 eq72
  have eq158 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3) = X2 := superpose eq157 eq124
  have eq174 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq157 eq158
  have eq175 (X0 X3 : G) : X0 = X3 := superpose eq174 eq174
  have eq180 (X0 : G) : sK0 ≠ X0 := superpose eq175 eq8
  subsumption eq180 eq175


@[equational_result]
theorem Equation16603_implies_Equation2 (G : Type*) [Magma G] (h : Equation16603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation16604_implies_Equation2 (G : Type*) [Magma G] (h : Equation16604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation16606_implies_Equation2 (G : Type*) [Magma G] (h : Equation16606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X3 ◇ X0) ◇ X0) ◇ X2) ◇ X2) = (X1 ◇ (((X0 ◇ ((((X3 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = (X2 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq7 eq9
  have eq19 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)))) = X4 := superpose eq9 eq7
  have eq28 (X0 X1 X2 : G) : (((((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq7 eq10
  have eq45 (X0 X1 X2 : G) : ((((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq15
  have eq57 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq15 eq7
  have eq77 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq45 eq28
  have eq85 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq77 eq57
  have eq92 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ ((X1 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)))) = X4 := superpose eq85 eq19
  have eq130 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) = X4 := superpose eq85 eq92
  have eq131 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X4 := superpose eq85 eq130
  have eq132 (X0 X1 X3 X4 : G) : (((X1 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X1)) = X4 := superpose eq85 eq131
  have eq133 (X0 X1 X3 X4 : G) : (((X1 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ (X0 ◇ X1)) = X4 := superpose eq85 eq132
  have eq134 (X0 X1 X3 X4 : G) : (((X1 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ X0) = X4 := superpose eq85 eq133
  have eq135 (X0 X1 X3 X4 : G) : ((X1 ◇ ((X3 ◇ X4) ◇ X4)) ◇ X0) = X4 := superpose eq85 eq134
  have eq136 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq85 eq135
  have eq141 (X0 X3 : G) : X0 = X3 := superpose eq136 eq136
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq149 eq141


@[equational_result]
theorem Equation16608_implies_Equation2 (G : Type*) [Magma G] (h : Equation16608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation16611_implies_Equation2 (G : Type*) [Magma G] (h : Equation16611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq73 eq15


@[equational_result]
theorem Equation16612_implies_Equation2 (G : Type*) [Magma G] (h : Equation16612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16614_implies_Equation2 (G : Type*) [Magma G] (h : Equation16614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq57 eq15


@[equational_result]
theorem Equation16615_implies_Equation2 (G : Type*) [Magma G] (h : Equation16615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16616_implies_Equation2 (G : Type*) [Magma G] (h : Equation16616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X4 ◇ X0) ◇ X0) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq75 eq15


@[equational_result]
theorem Equation16617_implies_Equation2 (G : Type*) [Magma G] (h : Equation16617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16619_implies_Equation2 (G : Type*) [Magma G] (h : Equation16619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X3 ◇ X0) ◇ X2) ◇ X0) ◇ X2) = (X1 ◇ (((X0 ◇ X1) ◇ ((((X3 ◇ X0) ◇ X2) ◇ X0) ◇ X2)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X3) ◇ ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X3)))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X2)) = (X2 ◇ (X0 ◇ X2)) := superpose eq7 eq9
  have eq32 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq10
  have eq39 (X0 X2 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq17 eq32
  have eq41 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) ◇ X3) = (((((X1 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) ◇ X3) := superpose eq9 eq39
  have eq46 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X3 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq10 eq39
  have eq71 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) ◇ X3) = ((X2 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq46 eq41
  have eq81 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) ◇ X3) = X2 := superpose eq39 eq71
  have eq82 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((((X3 ◇ X0) ◇ X2) ◇ X0) ◇ X2) := superpose eq81 eq9
  have eq115 (X0 X1 X2 X3 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) ◇ X3) = X2 := superpose eq82 eq39
  have eq130 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq7 eq115
  have eq131 (X0 X3 : G) : X0 = X3 := superpose eq7 eq130
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq207 eq131


@[equational_result]
theorem Equation16621_implies_Equation2 (G : Type*) [Magma G] (h : Equation16621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation16623_implies_Equation2 (G : Type*) [Magma G] (h : Equation16623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X3 ◇ X0) ◇ X2) ◇ X2) ◇ X2) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) ◇ X3) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X4 : G) : (X2 ◇ ((((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X2) ◇ X2) ◇ X2)) = X4 := superpose eq9 eq7
  have eq36 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq24 eq29
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq7 eq36
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq151 eq58


@[equational_result]
theorem Equation16625_implies_Equation2 (G : Type*) [Magma G] (h : Equation16625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq72 eq12


@[equational_result]
theorem Equation16629_implies_Equation2 (G : Type*) [Magma G] (h : Equation16629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation16631_implies_Equation2 (G : Type*) [Magma G] (h : Equation16631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation16632_implies_Equation2 (G : Type*) [Magma G] (h : Equation16632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq77 eq15


@[equational_result]
theorem Equation16633_implies_Equation2 (G : Type*) [Magma G] (h : Equation16633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ X0) ◇ X2) ◇ X4) ◇ X4) = (X1 ◇ (((X0 ◇ X1) ◇ X5) ◇ X5)) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ X4) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X6 X7 : G) : (X3 ◇ ((((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X7) ◇ X7)) = X6 := superpose eq9 eq7
  have eq41 (X2 X3 X6 : G) : (X3 ◇ X2) = X6 := superpose eq29 eq34
  have eq78 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq185 eq78


@[equational_result]
theorem Equation16634_implies_Equation2 (G : Type*) [Magma G] (h : Equation16634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16637_implies_Equation2 (G : Type*) [Magma G] (h : Equation16637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq66 eq15


@[equational_result]
theorem Equation16638_implies_Equation2 (G : Type*) [Magma G] (h : Equation16638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation16642_implies_Equation2 (G : Type*) [Magma G] (h : Equation16642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation16644_implies_Equation2 (G : Type*) [Magma G] (h : Equation16644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X3 ◇ X0) ◇ X3) ◇ X3) ◇ X2) = (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = (X4 ◇ (((X1 ◇ X2) ◇ X2) ◇ X4)) := superpose eq9 eq9
  have eq20 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ (X4 ◇ X1)) ◇ X3) ◇ X3) ◇ X4) = (X2 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0))) := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X3) = (((((X4 ◇ X0) ◇ X4) ◇ X4) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) := superpose eq7 eq9
  have eq23 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) ◇ X2) = X0 := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) = ((((X3 ◇ X1) ◇ X3) ◇ X3) ◇ X2) := superpose eq9 eq9
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0))) = X1 := superpose eq23 eq20
  have eq42 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) ◇ X0)) ◇ X1) = X3 := superpose eq9 eq10
  have eq46 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X2) ◇ (((X4 ◇ X0) ◇ X4) ◇ X4))) ◇ X1) ◇ X1) ◇ X3) = (X5 ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq10 eq9
  have eq54 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) = X1 := superpose eq7 eq23
  have eq78 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq23 eq31
  have eq154 (X0 X1 X4 : G) : (X4 ◇ (X0 ◇ X4)) = (X1 ◇ (X0 ◇ X1)) := superpose eq10 eq15
  have eq363 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X2) = (X2 ◇ (X3 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ X3))) := superpose eq24 eq31
  have eq388 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X2 ◇ X3) ◇ X3) ◇ (((X4 ◇ X1) ◇ X4) ◇ X4)))) = X2 := superpose eq24 eq31
  have eq763 (X0 X1 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) = X0 := superpose eq31 eq78
  have eq768 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) ◇ X0) = X2 := superpose eq78 eq23
  have eq970 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X3) = (X3 ◇ (X4 ◇ ((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1) ◇ X4))) := superpose eq21 eq31
  have eq1068 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ X2) ◇ X4) ◇ X4) = ((X3 ◇ (X3 ◇ ((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1) ◇ X3))) ◇ X3) := superpose eq21 eq763
  have eq1092 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) = X1 := superpose eq154 eq763
  have eq1135 (X2 X3 X4 : G) : (((X4 ◇ X2) ◇ X4) ◇ X4) = (((X3 ◇ X2) ◇ X3) ◇ X3) := superpose eq970 eq1068
  have eq1395 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq154 eq768
  have eq1555 (X0 X1 X2 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = X1 := superpose eq54 eq42
  have eq1631 (X0 X1 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = X1 := superpose eq7 eq1555
  have eq1675 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X0) := superpose eq1631 eq154
  have eq4789 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq1395 eq31
  have eq5042 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((((X4 ◇ X2) ◇ X4) ◇ X4) ◇ (((X5 ◇ X1) ◇ X5) ◇ X5))) = (X3 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq46 eq31
  have eq5332 (X0 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq4789 eq1092
  have eq5777 (X0 X1 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X1) = X1 := superpose eq1135 eq5332
  have eq5806 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq5777 eq1675
  have eq5829 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = (X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) := superpose eq5806 eq363
  have eq6949 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((((X4 ◇ X2) ◇ X4) ◇ X4) ◇ (((X5 ◇ X1) ◇ X5) ◇ X5))) = (X3 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq5806 eq5042
  have eq7177 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq7 eq5829
  have eq7241 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X3) ◇ (((X4 ◇ X1) ◇ X4) ◇ X4)))) = X2 := superpose eq7177 eq388
  have eq8033 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X3) ◇ (X1 ◇ X4)))) = X2 := superpose eq7177 eq7241
  have eq8050 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X1) = (X3 ◇ ((((X4 ◇ X2) ◇ X4) ◇ X4) ◇ (((X5 ◇ X1) ◇ X5) ◇ X5))) := superpose eq5806 eq6949
  have eq8051 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X1) = (X3 ◇ ((((X4 ◇ X2) ◇ X4) ◇ X4) ◇ (X1 ◇ X5))) := superpose eq7177 eq8050
  have eq8052 (X1 X2 X3 X4 X5 : G) : (X3 ◇ X1) = (X3 ◇ ((X2 ◇ X4) ◇ (X1 ◇ X5))) := superpose eq7177 eq8051
  have eq8053 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq8052 eq8033
  have eq8054 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq7177 eq8053
  have eq8055 (X0 X3 : G) : X0 = X3 := superpose eq8054 eq8054
  have eq8057 (X0 : G) : sK0 ≠ X0 := superpose eq8055 eq8
  subsumption eq8057 eq8055


@[equational_result]
theorem Equation16645_implies_Equation2 (G : Type*) [Magma G] (h : Equation16645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ X2)) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq75 eq14


@[equational_result]
theorem Equation16646_implies_Equation2 (G : Type*) [Magma G] (h : Equation16646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16648_implies_Equation2 (G : Type*) [Magma G] (h : Equation16648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq77 eq15


@[equational_result]
theorem Equation16649_implies_Equation2 (G : Type*) [Magma G] (h : Equation16649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation16650_implies_Equation2 (G : Type*) [Magma G] (h : Equation16650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X4 ◇ X0) ◇ X4) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation16651_implies_Equation2 (G : Type*) [Magma G] (h : Equation16651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16653_implies_Equation2 (G : Type*) [Magma G] (h : Equation16653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (((X3 ◇ X4) ◇ X5) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq36 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq11 eq7
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq36
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq129 eq47


@[equational_result]
theorem Equation16654_implies_Equation2 (G : Type*) [Magma G] (h : Equation16654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation16655_implies_Equation2 (G : Type*) [Magma G] (h : Equation16655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X3) ◇ ((((X4 ◇ X0) ◇ X5) ◇ X0) ◇ X5))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation16656_implies_Equation2 (G : Type*) [Magma G] (h : Equation16656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation16658_implies_Equation2 (G : Type*) [Magma G] (h : Equation16658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation16659_implies_Equation2 (G : Type*) [Magma G] (h : Equation16659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq79 eq18


@[equational_result]
theorem Equation16660_implies_Equation2 (G : Type*) [Magma G] (h : Equation16660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ X0) ◇ X4) ◇ X2) ◇ X4) = (X1 ◇ (((X0 ◇ X5) ◇ X1) ◇ X5)) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ X3) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X5 X7 : G) : (X3 ◇ ((((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ X7) ◇ X3) ◇ X7)) = X5 := superpose eq9 eq7
  have eq41 (X2 X3 X5 : G) : (X3 ◇ X2) = X5 := superpose eq29 eq34
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq188 eq73


@[equational_result]
theorem Equation16661_implies_Equation2 (G : Type*) [Magma G] (h : Equation16661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation16663_implies_Equation2 (G : Type*) [Magma G] (h : Equation16663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq82 eq18


@[equational_result]
theorem Equation16664_implies_Equation2 (G : Type*) [Magma G] (h : Equation16664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X2) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation16665_implies_Equation2 (G : Type*) [Magma G] (h : Equation16665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((((X4 ◇ X0) ◇ X5) ◇ X4) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation16666_implies_Equation2 (G : Type*) [Magma G] (h : Equation16666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16668_implies_Equation2 (G : Type*) [Magma G] (h : Equation16668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ X0) ◇ X4) ◇ X4) ◇ X2) = (X1 ◇ (((X0 ◇ X5) ◇ X5) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ ((((X4 ◇ X0) ◇ X5) ◇ X5) ◇ (X2 ◇ X3))) ◇ X1)) = X3 := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) ◇ X4) = X0 := superpose eq7 eq9
  have eq45 (X0 X1 X2 X3 X4 X7 X8 X9 : G) : (X3 ◇ ((X4 ◇ ((((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X7) ◇ X7) ◇ (X8 ◇ X9))) ◇ X3)) = X9 := superpose eq9 eq10
  have eq74 (X0 X3 X4 X9 : G) : (X3 ◇ ((X4 ◇ X0) ◇ X3)) = X9 := superpose eq29 eq45
  have eq87 (X0 X4 : G) : X0 = X4 := superpose eq7 eq74
  have eq193 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq193 eq87


@[equational_result]
theorem Equation16669_implies_Equation2 (G : Type*) [Magma G] (h : Equation16669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16670_implies_Equation2 (G : Type*) [Magma G] (h : Equation16670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ ((((X4 ◇ X0) ◇ X5) ◇ X5) ◇ X5)) ◇ ((((X4 ◇ X0) ◇ X5) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation16671_implies_Equation2 (G : Type*) [Magma G] (h : Equation16671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16673_implies_Equation2 (G : Type*) [Magma G] (h : Equation16673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation16674_implies_Equation2 (G : Type*) [Magma G] (h : Equation16674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16675_implies_Equation2 (G : Type*) [Magma G] (h : Equation16675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 X5 X6 X7 : G) : (X1 ◇ ((X0 ◇ X7) ◇ ((((X4 ◇ X0) ◇ X5) ◇ X6) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation16676_implies_Equation2 (G : Type*) [Magma G] (h : Equation16676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X5 X6 X7 : G) : (X1 ◇ (X0 ◇ ((((X5 ◇ X0) ◇ X6) ◇ X7) ◇ X7))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation16677_implies_Equation2 (G : Type*) [Magma G] (h : Equation16677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16679_implies_Equation2 (G : Type*) [Magma G] (h : Equation16679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X2) ◇ (((X0 ◇ X3) ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) = (X1 ◇ ((X0 ◇ ((((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) ◇ (X2 ◇ X1))) ◇ X1)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (((((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : ((((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq10
  have eq49 (X0 X1 X3 : G) : (X1 ◇ (((X0 ◇ X3) ◇ X3) ◇ X1)) = X3 := superpose eq17 eq7
  have eq51 (X0 X1 X2 : G) : (X1 ◇ (((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ X1)) = (((X0 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) ◇ ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) ◇ ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) := superpose eq7 eq29
  have eq55 (X0 X2 X3 : G) : (X3 ◇ ((X2 ◇ X3) ◇ X3)) = (((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) := superpose eq17 eq29
  have eq65 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq29 eq7
  have eq82 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq55 eq29
  have eq105 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq17 eq49
  have eq123 (X0 X1 X2 : G) : (((X0 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) ◇ ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) ◇ ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose eq105 eq51
  have eq127 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq105 eq65
  have eq130 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq105 eq82
  have eq137 (X0 X1 X2 : G) : ((((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X2 := superpose eq127 eq17
  have eq156 (X0 X1 X2 : G) : (((X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X1 := superpose eq127 eq123
  have eq181 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq127 eq137
  have eq187 (X0 X1 X2 : G) : ((X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X1 := superpose eq127 eq156
  have eq220 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X2) = X0 := superpose eq181 eq181
  have eq226 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq130 eq220
  have eq228 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X1 := superpose eq226 eq187
  have eq246 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X1 := superpose eq226 eq228
  have eq247 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X1 := superpose eq226 eq246
  have eq248 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq226 eq247
  have eq249 (X0 X3 : G) : X0 = X3 := superpose eq248 eq248
  have eq254 (X0 : G) : sK0 ≠ X0 := superpose eq249 eq8
  subsumption eq254 eq249


@[equational_result]
theorem Equation16681_implies_Equation2 (G : Type*) [Magma G] (h : Equation16681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation16683_implies_Equation2 (G : Type*) [Magma G] (h : Equation16683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2) ◇ (((X0 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X3 ◇ X1) ◇ X1)) = (((X0 ◇ X3) ◇ ((((X2 ◇ X1) ◇ X0) ◇ X1) ◇ X1)) ◇ ((((X2 ◇ X1) ◇ X0) ◇ X1) ◇ X1)) := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq10 eq7
  have eq22 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) = X3 := superpose eq11 eq9
  have eq52 (X0 X2 X4 : G) : (X0 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X4 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))) = X4 := superpose eq22 eq19
  have eq59 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X3 ◇ X2) ◇ X0) := superpose eq7 eq19
  have eq62 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) = X1 := superpose eq19 eq7
  have eq99 (X0 X2 X4 X5 : G) : (X0 ◇ X4) = ((X5 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X4) := superpose eq22 eq59
  have eq185 (X0 X2 X4 : G) : (X0 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))) = X4 := superpose eq99 eq52
  have eq188 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq62 eq185
  have eq307 (X0 X3 : G) : X0 = X3 := superpose eq188 eq188
  have eq546 (X0 : G) : sK0 ≠ X0 := superpose eq307 eq8
  subsumption eq546 eq307


@[equational_result]
theorem Equation16685_implies_Equation2 (G : Type*) [Magma G] (h : Equation16685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation16689_implies_Equation2 (G : Type*) [Magma G] (h : Equation16689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation16691_implies_Equation2 (G : Type*) [Magma G] (h : Equation16691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation16692_implies_Equation2 (G : Type*) [Magma G] (h : Equation16692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq63 eq15


@[equational_result]
theorem Equation16693_implies_Equation2 (G : Type*) [Magma G] (h : Equation16693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X3) ◇ (((X0 ◇ X4) ◇ X5) ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X0) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X4 ◇ X0) ◇ X5) ◇ X5))) = X1 := superpose eq9 eq7
  have eq26 (X0 X1 X4 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X4) ◇ X4) := superpose eq9 eq7
  have eq28 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X3) ◇ (X0 ◇ X4)) = X4 := superpose eq26 eq9
  have eq36 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X0))) = X1 := superpose eq26 eq25
  have eq40 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X0))) = X3 := superpose eq26 eq11
  have eq41 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X4)) = X4 := superpose eq26 eq28
  have eq58 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq41 eq36
  have eq67 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq58 eq40
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq41 eq67
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq89 eq71


@[equational_result]
theorem Equation16694_implies_Equation2 (G : Type*) [Magma G] (h : Equation16694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16696_implies_Equation2 (G : Type*) [Magma G] (h : Equation16696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) ◇ X2) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq7
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ X2) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) := superpose eq7 eq11
  have eq64 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = (((X3 ◇ X2) ◇ X2) ◇ X0) := superpose eq7 eq19
  have eq66 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq19 eq19
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ (((((X2 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ X1)) = (X0 ◇ ((((X3 ◇ X1) ◇ X1) ◇ X1) ◇ X1)) := superpose eq7 eq23
  have eq100 (X0 X1 X2 : G) : ((((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) := superpose eq23 eq7
  have eq101 (X0 X1 X2 X3 : G) : (X2 ◇ (((((X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X2)) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq23 eq10
  have eq131 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (((X3 ◇ X1) ◇ X1) ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq23 eq64
  have eq154 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X1 := superpose eq64 eq7
  have eq231 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq154 eq14
  have eq243 (X0 X1 X3 : G) : (X0 ◇ ((((X3 ◇ X1) ◇ X1) ◇ X1) ◇ X1)) = X1 := superpose eq231 eq74
  have eq248 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq243 eq131
  have eq251 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ (((((X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X2)) := superpose eq248 eq101
  have eq252 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq248 eq100
  have eq254 (X0 X1 X2 : G) : ((((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq231 eq252
  have eq255 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) := superpose eq254 eq251
  have eq256 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq154 eq255
  have eq258 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq256 eq66
  have eq345 (X0 X1 : G) : X0 = X1 := superpose eq7 eq258
  have eq422 (X0 : G) : sK0 ≠ X0 := superpose eq345 eq8
  subsumption eq422 eq345


@[equational_result]
theorem Equation16698_implies_Equation2 (G : Type*) [Magma G] (h : Equation16698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq72 eq12


@[equational_result]
theorem Equation16700_implies_Equation2 (G : Type*) [Magma G] (h : Equation16700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16701_implies_Equation2 (G : Type*) [Magma G] (h : Equation16701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16702_implies_Equation2 (G : Type*) [Magma G] (h : Equation16702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16704_implies_Equation2 (G : Type*) [Magma G] (h : Equation16704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16705_implies_Equation2 (G : Type*) [Magma G] (h : Equation16705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16706_implies_Equation2 (G : Type*) [Magma G] (h : Equation16706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16708_implies_Equation2 (G : Type*) [Magma G] (h : Equation16708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16709_implies_Equation2 (G : Type*) [Magma G] (h : Equation16709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16710_implies_Equation2 (G : Type*) [Magma G] (h : Equation16710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16711_implies_Equation2 (G : Type*) [Magma G] (h : Equation16711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16715_implies_Equation2 (G : Type*) [Magma G] (h : Equation16715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation16717_implies_Equation2 (G : Type*) [Magma G] (h : Equation16717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16718_implies_Equation2 (G : Type*) [Magma G] (h : Equation16718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16719_implies_Equation2 (G : Type*) [Magma G] (h : Equation16719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16721_implies_Equation2 (G : Type*) [Magma G] (h : Equation16721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16722_implies_Equation2 (G : Type*) [Magma G] (h : Equation16722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16723_implies_Equation2 (G : Type*) [Magma G] (h : Equation16723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16725_implies_Equation2 (G : Type*) [Magma G] (h : Equation16725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16726_implies_Equation2 (G : Type*) [Magma G] (h : Equation16726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16727_implies_Equation2 (G : Type*) [Magma G] (h : Equation16727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16728_implies_Equation2 (G : Type*) [Magma G] (h : Equation16728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16730_implies_Equation2 (G : Type*) [Magma G] (h : Equation16730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X4 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X5) ◇ X0) ◇ ((X2 ◇ X1) ◇ X3)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq25 (X0 X1 X3 X4 X5 X6 X7 : G) : (X6 ◇ (((X3 ◇ X0) ◇ X4) ◇ X6)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X5 ◇ X6) ◇ X7)) := superpose eq11 eq11
  have eq34 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq11 eq7
  have eq47 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq13
  have eq50 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X5) = (X1 ◇ (((((X2 ◇ X3) ◇ X4) ◇ X0) ◇ X3) ◇ X1)) := superpose eq7 eq13
  have eq93 (X0 X3 X4 X6 : G) : (X6 ◇ (((X3 ◇ X0) ◇ X4) ◇ X6)) = X0 := superpose eq47 eq25
  have eq94 (X0 X5 : G) : (X0 ◇ X5) = X0 := superpose eq93 eq50
  have eq95 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X0) = X1 := superpose eq94 eq34
  have eq113 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = X1 := superpose eq94 eq95
  have eq114 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq94 eq113
  have eq115 (X0 X3 : G) : X0 = X3 := superpose eq114 eq114
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq115 eq8
  subsumption eq117 eq115


@[equational_result]
theorem Equation16731_implies_Equation2 (G : Type*) [Magma G] (h : Equation16731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X2)) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq153 eq57


@[equational_result]
theorem Equation16732_implies_Equation2 (G : Type*) [Magma G] (h : Equation16732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3) ◇ (((X0 ◇ X4) ◇ X5) ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ ((((X3 ◇ (X2 ◇ X1)) ◇ X4) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq22 (X0 X1 X4 X5 X6 : G) : (X1 ◇ ((X0 ◇ X6) ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))) = X6 := superpose eq9 eq7
  have eq34 (X0 X1 X2 X3 X7 X8 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X2) ◇ (((X7 ◇ X8) ◇ X0) ◇ X8)))) = X3 := superpose eq9 eq10
  have eq50 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq22 eq34
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq50
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq148 eq51


@[equational_result]
theorem Equation16733_implies_Equation2 (G : Type*) [Magma G] (h : Equation16733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation16735_implies_Equation2 (G : Type*) [Magma G] (h : Equation16735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16736_implies_Equation2 (G : Type*) [Magma G] (h : Equation16736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16737_implies_Equation2 (G : Type*) [Magma G] (h : Equation16737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16738_implies_Equation2 (G : Type*) [Magma G] (h : Equation16738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16740_implies_Equation2 (G : Type*) [Magma G] (h : Equation16740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16741_implies_Equation2 (G : Type*) [Magma G] (h : Equation16741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16742_implies_Equation2 (G : Type*) [Magma G] (h : Equation16742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16743_implies_Equation2 (G : Type*) [Magma G] (h : Equation16743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16745_implies_Equation2 (G : Type*) [Magma G] (h : Equation16745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16746_implies_Equation2 (G : Type*) [Magma G] (h : Equation16746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16747_implies_Equation2 (G : Type*) [Magma G] (h : Equation16747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16748_implies_Equation2 (G : Type*) [Magma G] (h : Equation16748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16750_implies_Equation2 (G : Type*) [Magma G] (h : Equation16750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16751_implies_Equation2 (G : Type*) [Magma G] (h : Equation16751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16752_implies_Equation2 (G : Type*) [Magma G] (h : Equation16752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16753_implies_Equation2 (G : Type*) [Magma G] (h : Equation16753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16754_implies_Equation2 (G : Type*) [Magma G] (h : Equation16754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X1) ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16756_implies_Equation2 (G : Type*) [Magma G] (h : Equation16756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X3 ◇ X3) ◇ X0) ◇ X0) ◇ (X2 ◇ X2)) = (X1 ◇ ((X0 ◇ ((((X3 ◇ X3) ◇ X0) ◇ X0) ◇ (X2 ◇ X2))) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ (((X2 ◇ X2) ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq10 eq7
  have eq20 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X2)) = ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq28 (X0 X1 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq20
  have eq30 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ X0) := superpose eq10 eq15
  have eq42 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ (((X2 ◇ X2) ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq30 eq10
  have eq52 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq30 eq28
  have eq53 (X0 X3 : G) : (((X0 ◇ X0) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq30 eq42
  have eq68 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq53 eq30
  have eq72 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq68 eq52
  have eq74 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq15 eq72
  have eq79 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq74 eq15
  have eq81 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq74 eq30
  have eq84 (X0 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq74 eq53
  have eq94 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq74 eq81
  have eq100 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X3 := superpose eq74 eq84
  have eq138 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq100 eq94
  have eq143 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq138 eq79
  have eq147 (X0 X2 : G) : X0 = X2 := superpose eq143 eq143
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq147 eq8
  subsumption eq155 eq147


@[equational_result]
theorem Equation16757_implies_Equation2 (G : Type*) [Magma G] (h : Equation16757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X3) ◇ X3) ◇ ((((X2 ◇ X2) ◇ X0) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16758_implies_Equation2 (G : Type*) [Magma G] (h : Equation16758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16762_implies_Equation2 (G : Type*) [Magma G] (h : Equation16762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq72 eq12


@[equational_result]
theorem Equation16765_implies_Equation2 (G : Type*) [Magma G] (h : Equation16765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X3) ◇ ((((X2 ◇ X2) ◇ X0) ◇ X2) ◇ X2)) ◇ ((((X2 ◇ X2) ◇ X0) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16766_implies_Equation2 (G : Type*) [Magma G] (h : Equation16766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16768_implies_Equation2 (G : Type*) [Magma G] (h : Equation16768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation16769_implies_Equation2 (G : Type*) [Magma G] (h : Equation16769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X4) ◇ X5) ◇ ((((X2 ◇ X2) ◇ X0) ◇ X3) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16770_implies_Equation2 (G : Type*) [Magma G] (h : Equation16770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X4 ◇ X4) ◇ X0) ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16771_implies_Equation2 (G : Type*) [Magma G] (h : Equation16771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16775_implies_Equation2 (G : Type*) [Magma G] (h : Equation16775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation16777_implies_Equation2 (G : Type*) [Magma G] (h : Equation16777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16778_implies_Equation2 (G : Type*) [Magma G] (h : Equation16778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16779_implies_Equation2 (G : Type*) [Magma G] (h : Equation16779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16781_implies_Equation2 (G : Type*) [Magma G] (h : Equation16781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16782_implies_Equation2 (G : Type*) [Magma G] (h : Equation16782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16783_implies_Equation2 (G : Type*) [Magma G] (h : Equation16783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16785_implies_Equation2 (G : Type*) [Magma G] (h : Equation16785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16786_implies_Equation2 (G : Type*) [Magma G] (h : Equation16786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16787_implies_Equation2 (G : Type*) [Magma G] (h : Equation16787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16788_implies_Equation2 (G : Type*) [Magma G] (h : Equation16788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16790_implies_Equation2 (G : Type*) [Magma G] (h : Equation16790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X3 ◇ X3) ◇ X3) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X1 ◇ X4)) := superpose eq9 eq9
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X2) ◇ X2) ◇ (((X3 ◇ X3) ◇ X3) ◇ X1)) ◇ ((X4 ◇ X4) ◇ X4)) = (((X5 ◇ X5) ◇ X5) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq9
  have eq20 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (((X2 ◇ X2) ◇ X2) ◇ X0)) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := superpose eq7 eq9
  have eq28 (X0 X1 X5 : G) : (((X5 ◇ X5) ◇ X5) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq20 eq18
  have eq96 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq15 eq28
  have eq133 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X2 ◇ (X3 ◇ X2))) = X3 := superpose eq96 eq28
  have eq139 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq96 eq15
  have eq143 (X0 X1 X2 : G) : ((X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0)) ◇ X2) = X2 := superpose eq96 eq10
  have eq162 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq7 eq143
  have eq163 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X1)) = X0 := superpose eq162 eq7
  have eq164 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X3 ◇ X3) ◇ X3) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq162 eq9
  have eq172 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := superpose eq162 eq20
  have eq223 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X0 := superpose eq162 eq163
  have eq224 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X3 ◇ X3) ◇ X3) ◇ X0) ◇ X2) := superpose eq162 eq164
  have eq225 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X3 ◇ X3) ◇ X0) ◇ X2) := superpose eq162 eq224
  have eq226 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq162 eq225
  have eq254 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X3 ◇ X3)) = X0 := superpose eq162 eq172
  have eq255 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) = X0 := superpose eq162 eq254
  have eq256 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq162 eq255
  have eq257 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq162 eq256
  have eq258 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq162 eq257
  have eq260 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X2))) = X3 := superpose eq258 eq133
  have eq261 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = X1 := superpose eq260 eq139
  have eq265 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X0 := superpose eq261 eq226
  have eq270 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq265 eq223
  have eq274 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq270 eq258
  have eq278 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq270 eq274
  have eq288 (X0 X1 : G) : X0 = X1 := superpose eq270 eq278
  have eq298 (X0 : G) : sK0 ≠ X0 := superpose eq288 eq8
  subsumption eq298 eq288


@[equational_result]
theorem Equation16791_implies_Equation2 (G : Type*) [Magma G] (h : Equation16791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X0) ◇ X2)) ◇ X3) ◇ ((((X2 ◇ X2) ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16792_implies_Equation2 (G : Type*) [Magma G] (h : Equation16792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation16794_implies_Equation2 (G : Type*) [Magma G] (h : Equation16794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16795_implies_Equation2 (G : Type*) [Magma G] (h : Equation16795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16796_implies_Equation2 (G : Type*) [Magma G] (h : Equation16796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16798_implies_Equation2 (G : Type*) [Magma G] (h : Equation16798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation16799_implies_Equation2 (G : Type*) [Magma G] (h : Equation16799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16800_implies_Equation2 (G : Type*) [Magma G] (h : Equation16800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16802_implies_Equation2 (G : Type*) [Magma G] (h : Equation16802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16803_implies_Equation2 (G : Type*) [Magma G] (h : Equation16803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16804_implies_Equation2 (G : Type*) [Magma G] (h : Equation16804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16805_implies_Equation2 (G : Type*) [Magma G] (h : Equation16805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16807_implies_Equation2 (G : Type*) [Magma G] (h : Equation16807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X4 ◇ X4) ◇ X5) ◇ X0) ◇ ((X2 ◇ X2) ◇ X3)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq35 (X0 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = X0 := superpose eq9 eq10
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq35
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq154 eq67


@[equational_result]
theorem Equation16808_implies_Equation2 (G : Type*) [Magma G] (h : Equation16808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X4) ◇ X5) ◇ ((((X2 ◇ X2) ◇ X3) ◇ X0) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16809_implies_Equation2 (G : Type*) [Magma G] (h : Equation16809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ ((((X3 ◇ X3) ◇ X4) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16810_implies_Equation2 (G : Type*) [Magma G] (h : Equation16810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16812_implies_Equation2 (G : Type*) [Magma G] (h : Equation16812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16813_implies_Equation2 (G : Type*) [Magma G] (h : Equation16813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16814_implies_Equation2 (G : Type*) [Magma G] (h : Equation16814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16815_implies_Equation2 (G : Type*) [Magma G] (h : Equation16815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16817_implies_Equation2 (G : Type*) [Magma G] (h : Equation16817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16818_implies_Equation2 (G : Type*) [Magma G] (h : Equation16818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16819_implies_Equation2 (G : Type*) [Magma G] (h : Equation16819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16820_implies_Equation2 (G : Type*) [Magma G] (h : Equation16820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16822_implies_Equation2 (G : Type*) [Magma G] (h : Equation16822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16823_implies_Equation2 (G : Type*) [Magma G] (h : Equation16823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16824_implies_Equation2 (G : Type*) [Magma G] (h : Equation16824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16825_implies_Equation2 (G : Type*) [Magma G] (h : Equation16825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16827_implies_Equation2 (G : Type*) [Magma G] (h : Equation16827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16828_implies_Equation2 (G : Type*) [Magma G] (h : Equation16828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16829_implies_Equation2 (G : Type*) [Magma G] (h : Equation16829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16830_implies_Equation2 (G : Type*) [Magma G] (h : Equation16830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16831_implies_Equation2 (G : Type*) [Magma G] (h : Equation16831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16833_implies_Equation2 (G : Type*) [Magma G] (h : Equation16833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (((X3 ◇ X4) ◇ X5) ◇ X5)) ◇ X0) = X5 := superpose eq7 eq7
  have eq39 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X1)) = X4 := superpose eq11 eq7
  have eq46 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X1)) = X4 := superpose eq11 eq39
  have eq109 (X0 X4 : G) : X0 = X4 := superpose eq7 eq46
  have eq205 (X0 : G) : sK0 ≠ X0 := superpose eq109 eq8
  subsumption eq205 eq109


@[equational_result]
theorem Equation16834_implies_Equation2 (G : Type*) [Magma G] (h : Equation16834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16835_implies_Equation2 (G : Type*) [Magma G] (h : Equation16835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X5) ◇ ((((X3 ◇ X4) ◇ X0) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16836_implies_Equation2 (G : Type*) [Magma G] (h : Equation16836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16838_implies_Equation2 (G : Type*) [Magma G] (h : Equation16838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X1) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X4 ◇ X5) ◇ X0) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq30 (X0 X1 X4 X5 X6 : G) : (X6 ◇ (((X4 ◇ X5) ◇ X6) ◇ X6)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X4 ◇ X5)) := superpose eq10 eq10
  have eq39 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ X1) ◇ (X6 ◇ X7))) ◇ (X8 ◇ X9)) ◇ (X8 ◇ X9)) = ((X6 ◇ X7) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X6 ◇ X7))) := superpose eq10 eq10
  have eq41 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ (X5 ◇ X6)) ◇ (X5 ◇ X6)) = X0 := superpose eq7 eq10
  have eq44 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq10 eq9
  have eq58 (X0 X1 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X4 ◇ X5)) = X5 := superpose eq9 eq30
  have eq60 (X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ X1) ◇ (X6 ◇ X7))) ◇ (X8 ◇ X9)) ◇ (X8 ◇ X9)) = ((X6 ◇ X7) ◇ X7) := superpose eq58 eq39
  have eq62 (X6 X7 : G) : (X6 ◇ X7) = ((X6 ◇ X7) ◇ X7) := superpose eq41 eq60
  have eq65 (X0 X1 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X1)) = X5 := superpose eq62 eq9
  have eq93 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X1 := superpose eq65 eq44
  have eq100 (X0 X4 : G) : X0 = X4 := superpose eq93 eq93
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq100 eq8
  subsumption eq112 eq100


@[equational_result]
theorem Equation16839_implies_Equation2 (G : Type*) [Magma G] (h : Equation16839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X1) ◇ X2)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq168 eq64


@[equational_result]
theorem Equation16840_implies_Equation2 (G : Type*) [Magma G] (h : Equation16840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X1) ◇ ((((X3 ◇ X4) ◇ X0) ◇ X2) ◇ X4))) = X5 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq75 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq185 eq75


@[equational_result]
theorem Equation16841_implies_Equation2 (G : Type*) [Magma G] (h : Equation16841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation16843_implies_Equation2 (G : Type*) [Magma G] (h : Equation16843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X2) ◇ X1)) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq9
  have eq74 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq166 eq74


@[equational_result]
theorem Equation16844_implies_Equation2 (G : Type*) [Magma G] (h : Equation16844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X0 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X2) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16845_implies_Equation2 (G : Type*) [Magma G] (h : Equation16845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X2) ◇ ((((X3 ◇ X4) ◇ X0) ◇ X3) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16846_implies_Equation2 (G : Type*) [Magma G] (h : Equation16846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16848_implies_Equation2 (G : Type*) [Magma G] (h : Equation16848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ ((((X3 ◇ X4) ◇ X0) ◇ X4) ◇ X2)) ◇ X1)) = X5 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq9
  have eq85 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq191 eq85


@[equational_result]
theorem Equation16849_implies_Equation2 (G : Type*) [Magma G] (h : Equation16849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16850_implies_Equation2 (G : Type*) [Magma G] (h : Equation16850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X5) ◇ ((((X3 ◇ X4) ◇ X0) ◇ X4) ◇ X4)) ◇ ((((X3 ◇ X4) ◇ X0) ◇ X4) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16851_implies_Equation2 (G : Type*) [Magma G] (h : Equation16851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation16853_implies_Equation2 (G : Type*) [Magma G] (h : Equation16853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation16854_implies_Equation2 (G : Type*) [Magma G] (h : Equation16854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16855_implies_Equation2 (G : Type*) [Magma G] (h : Equation16855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 X6 X7 : G) : (X1 ◇ (((X0 ◇ X6) ◇ X7) ◇ ((((X3 ◇ X4) ◇ X0) ◇ X5) ◇ X4))) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16856_implies_Equation2 (G : Type*) [Magma G] (h : Equation16856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 X6 X7 : G) : (X1 ◇ (X0 ◇ ((((X5 ◇ X6) ◇ X0) ◇ X7) ◇ X7))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq11
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16857_implies_Equation2 (G : Type*) [Magma G] (h : Equation16857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation16859_implies_Equation2 (G : Type*) [Magma G] (h : Equation16859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) ◇ (X3 ◇ X4)) ◇ ((X0 ◇ X5) ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) ◇ (X3 ◇ X4)))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X4 ◇ X5) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X3 ◇ X4) ◇ (X2 ◇ X1)) ◇ X0) ◇ (X2 ◇ X1)) := superpose eq7 eq9
  have eq19 (X0 X4 X5 : G) : ((X4 ◇ (X0 ◇ X4)) ◇ ((X0 ◇ X5) ◇ (X4 ◇ (X0 ◇ X4)))) = X5 := superpose eq14 eq10
  have eq31 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))))) = X3 := superpose eq19 eq7
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((((X3 ◇ X4) ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2)))) ◇ (X1 ◇ X2))) = (X0 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2))) := superpose eq19 eq11
  have eq77 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq11 eq9
  have eq80 (X0 X1 X4 X5 : G) : ((X4 ◇ X5) ◇ X0) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq11 eq9
  have eq118 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) ◇ X0) := superpose eq19 eq77
  have eq124 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq77 eq9
  have eq130 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq77 eq19
  have eq145 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2))) = (X0 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2))) := superpose eq118 eq64
  have eq150 (X0 X1 X4 X5 : G) : (X1 ◇ X0) = ((X4 ◇ X5) ◇ X0) := superpose eq124 eq80
  have eq151 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2))) = X4 := superpose eq130 eq145
  have eq154 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq151 eq31
  have eq160 (X0 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq77 eq150
  have eq235 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq160 eq154
  have eq237 (X0 X4 : G) : X0 = X4 := superpose eq7 eq235
  have eq360 (X0 : G) : sK0 ≠ X0 := superpose eq237 eq8
  subsumption eq360 eq237


@[equational_result]
theorem Equation16860_implies_Equation2 (G : Type*) [Magma G] (h : Equation16860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X5) ◇ X2)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq134 eq46


@[equational_result]
theorem Equation16861_implies_Equation2 (G : Type*) [Magma G] (h : Equation16861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X5) ◇ ((((X3 ◇ X4) ◇ X2) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq156 eq57


@[equational_result]
theorem Equation16862_implies_Equation2 (G : Type*) [Magma G] (h : Equation16862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation16864_implies_Equation2 (G : Type*) [Magma G] (h : Equation16864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16865_implies_Equation2 (G : Type*) [Magma G] (h : Equation16865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16866_implies_Equation2 (G : Type*) [Magma G] (h : Equation16866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16867_implies_Equation2 (G : Type*) [Magma G] (h : Equation16867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16869_implies_Equation2 (G : Type*) [Magma G] (h : Equation16869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16870_implies_Equation2 (G : Type*) [Magma G] (h : Equation16870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16871_implies_Equation2 (G : Type*) [Magma G] (h : Equation16871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16872_implies_Equation2 (G : Type*) [Magma G] (h : Equation16872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16874_implies_Equation2 (G : Type*) [Magma G] (h : Equation16874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16875_implies_Equation2 (G : Type*) [Magma G] (h : Equation16875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16876_implies_Equation2 (G : Type*) [Magma G] (h : Equation16876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16877_implies_Equation2 (G : Type*) [Magma G] (h : Equation16877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16879_implies_Equation2 (G : Type*) [Magma G] (h : Equation16879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16880_implies_Equation2 (G : Type*) [Magma G] (h : Equation16880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16881_implies_Equation2 (G : Type*) [Magma G] (h : Equation16881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16882_implies_Equation2 (G : Type*) [Magma G] (h : Equation16882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16883_implies_Equation2 (G : Type*) [Magma G] (h : Equation16883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16885_implies_Equation2 (G : Type*) [Magma G] (h : Equation16885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X4 ◇ X5) ◇ X4) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq36 (X0 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = X0 := superpose eq9 eq10
  have eq72 (X0 X4 : G) : X0 = X4 := superpose eq7 eq36
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq162 eq72


@[equational_result]
theorem Equation16886_implies_Equation2 (G : Type*) [Magma G] (h : Equation16886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16887_implies_Equation2 (G : Type*) [Magma G] (h : Equation16887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X5) ◇ ((((X3 ◇ X4) ◇ X3) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16888_implies_Equation2 (G : Type*) [Magma G] (h : Equation16888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16890_implies_Equation2 (G : Type*) [Magma G] (h : Equation16890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16891_implies_Equation2 (G : Type*) [Magma G] (h : Equation16891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16892_implies_Equation2 (G : Type*) [Magma G] (h : Equation16892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16893_implies_Equation2 (G : Type*) [Magma G] (h : Equation16893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16895_implies_Equation2 (G : Type*) [Magma G] (h : Equation16895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16896_implies_Equation2 (G : Type*) [Magma G] (h : Equation16896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16897_implies_Equation2 (G : Type*) [Magma G] (h : Equation16897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16898_implies_Equation2 (G : Type*) [Magma G] (h : Equation16898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16900_implies_Equation2 (G : Type*) [Magma G] (h : Equation16900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16901_implies_Equation2 (G : Type*) [Magma G] (h : Equation16901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16902_implies_Equation2 (G : Type*) [Magma G] (h : Equation16902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16903_implies_Equation2 (G : Type*) [Magma G] (h : Equation16903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16905_implies_Equation2 (G : Type*) [Magma G] (h : Equation16905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16906_implies_Equation2 (G : Type*) [Magma G] (h : Equation16906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16907_implies_Equation2 (G : Type*) [Magma G] (h : Equation16907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16908_implies_Equation2 (G : Type*) [Magma G] (h : Equation16908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16909_implies_Equation2 (G : Type*) [Magma G] (h : Equation16909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16911_implies_Equation2 (G : Type*) [Magma G] (h : Equation16911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ ((((X3 ◇ X4) ◇ X4) ◇ X0) ◇ X2)) ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (((X3 ◇ X4) ◇ X4) ◇ X5)) ◇ X0) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X1)) = X4 := superpose eq7 eq9
  have eq149 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X1)) = X4 := superpose eq11 eq18
  have eq167 (X0 X4 : G) : X0 = X4 := superpose eq7 eq149
  have eq305 (X0 : G) : sK0 ≠ X0 := superpose eq167 eq8
  subsumption eq305 eq167


@[equational_result]
theorem Equation16912_implies_Equation2 (G : Type*) [Magma G] (h : Equation16912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation16913_implies_Equation2 (G : Type*) [Magma G] (h : Equation16913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ ((((X3 ◇ X4) ◇ X4) ◇ X0) ◇ X4)) ◇ X5) ◇ ((((X3 ◇ X4) ◇ X4) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16914_implies_Equation2 (G : Type*) [Magma G] (h : Equation16914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation16916_implies_Equation2 (G : Type*) [Magma G] (h : Equation16916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16917_implies_Equation2 (G : Type*) [Magma G] (h : Equation16917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16918_implies_Equation2 (G : Type*) [Magma G] (h : Equation16918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16919_implies_Equation2 (G : Type*) [Magma G] (h : Equation16919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16921_implies_Equation2 (G : Type*) [Magma G] (h : Equation16921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16922_implies_Equation2 (G : Type*) [Magma G] (h : Equation16922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16923_implies_Equation2 (G : Type*) [Magma G] (h : Equation16923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16924_implies_Equation2 (G : Type*) [Magma G] (h : Equation16924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16926_implies_Equation2 (G : Type*) [Magma G] (h : Equation16926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation16927_implies_Equation2 (G : Type*) [Magma G] (h : Equation16927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16928_implies_Equation2 (G : Type*) [Magma G] (h : Equation16928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16929_implies_Equation2 (G : Type*) [Magma G] (h : Equation16929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16931_implies_Equation2 (G : Type*) [Magma G] (h : Equation16931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16932_implies_Equation2 (G : Type*) [Magma G] (h : Equation16932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16933_implies_Equation2 (G : Type*) [Magma G] (h : Equation16933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16934_implies_Equation2 (G : Type*) [Magma G] (h : Equation16934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16935_implies_Equation2 (G : Type*) [Magma G] (h : Equation16935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16937_implies_Equation2 (G : Type*) [Magma G] (h : Equation16937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X7 : G) : (X1 ◇ ((X0 ◇ X7) ◇ X1)) = X7 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq51 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq14
  have eq181 (X0 X5 : G) : X0 = X5 := superpose eq7 eq51
  have eq331 (X0 : G) : sK0 ≠ X0 := superpose eq181 eq8
  subsumption eq331 eq181


@[equational_result]
theorem Equation16938_implies_Equation2 (G : Type*) [Magma G] (h : Equation16938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16939_implies_Equation2 (G : Type*) [Magma G] (h : Equation16939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 X6 X7 : G) : (X1 ◇ (((X0 ◇ X6) ◇ X7) ◇ ((((X3 ◇ X4) ◇ X5) ◇ X0) ◇ X4))) = X7 := superpose eq7 eq7
  have eq13 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation16940_implies_Equation2 (G : Type*) [Magma G] (h : Equation16940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 X6 X7 : G) : (X1 ◇ ((X0 ◇ X7) ◇ ((((X4 ◇ X5) ◇ X6) ◇ X0) ◇ X6))) = X7 := superpose eq7 eq7
  have eq13 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation16941_implies_Equation2 (G : Type*) [Magma G] (h : Equation16941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X0) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation16943_implies_Equation2 (G : Type*) [Magma G] (h : Equation16943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16944_implies_Equation2 (G : Type*) [Magma G] (h : Equation16944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16945_implies_Equation2 (G : Type*) [Magma G] (h : Equation16945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16946_implies_Equation2 (G : Type*) [Magma G] (h : Equation16946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16947_implies_Equation2 (G : Type*) [Magma G] (h : Equation16947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X1) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16949_implies_Equation2 (G : Type*) [Magma G] (h : Equation16949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16950_implies_Equation2 (G : Type*) [Magma G] (h : Equation16950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16951_implies_Equation2 (G : Type*) [Magma G] (h : Equation16951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16952_implies_Equation2 (G : Type*) [Magma G] (h : Equation16952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16953_implies_Equation2 (G : Type*) [Magma G] (h : Equation16953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X2) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16955_implies_Equation2 (G : Type*) [Magma G] (h : Equation16955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16956_implies_Equation2 (G : Type*) [Magma G] (h : Equation16956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16957_implies_Equation2 (G : Type*) [Magma G] (h : Equation16957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16958_implies_Equation2 (G : Type*) [Magma G] (h : Equation16958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16959_implies_Equation2 (G : Type*) [Magma G] (h : Equation16959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X3) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16961_implies_Equation2 (G : Type*) [Magma G] (h : Equation16961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation16962_implies_Equation2 (G : Type*) [Magma G] (h : Equation16962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16963_implies_Equation2 (G : Type*) [Magma G] (h : Equation16963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16964_implies_Equation2 (G : Type*) [Magma G] (h : Equation16964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16965_implies_Equation2 (G : Type*) [Magma G] (h : Equation16965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16967_implies_Equation2 (G : Type*) [Magma G] (h : Equation16967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X5) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16968_implies_Equation2 (G : Type*) [Magma G] (h : Equation16968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X5) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16969_implies_Equation2 (G : Type*) [Magma G] (h : Equation16969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X5) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16970_implies_Equation2 (G : Type*) [Magma G] (h : Equation16970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X5) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16971_implies_Equation2 (G : Type*) [Magma G] (h : Equation16971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X5) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation16972_implies_Equation2 (G : Type*) [Magma G] (h : Equation16972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X5) ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17215_implies_Equation2 (G : Type*) [Magma G] (h : Equation17215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X2))))) := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))))) = X0 := superpose eq7 eq10
  have eq20 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq10
  have eq31 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq20
  have eq32 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq20
  have eq33 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq20 eq20
  have eq37 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq20 eq10
  have eq69 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq31 eq20
  have eq98 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq33 eq10
  have eq125 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq13 eq18
  have eq149 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq125 eq98
  have eq156 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq125 eq69
  have eq167 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq156 eq33
  have eq181 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ X0) := superpose eq7 eq125
  have eq214 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq181 eq167
  have eq224 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq181 eq32
  have eq229 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq181 eq15
  have eq268 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq214 eq11
  have eq271 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq268 eq214
  have eq273 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq271 eq37
  have eq302 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq271 eq224
  have eq303 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq271 eq302
  have eq304 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq303 eq273
  have eq308 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq304 eq149
  have eq309 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq125 eq308
  have eq310 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq271 eq309
  have eq320 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq310 eq303
  have eq346 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq320 eq229
  have eq347 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq310 eq346
  have eq348 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq310 eq347
  have eq349 (X0 X3 : G) : X0 = X3 := superpose eq348 eq348
  have eq351 (X0 : G) : sK0 ≠ X0 := superpose eq349 eq8
  subsumption eq351 eq349


@[equational_result]
theorem Equation17218_implies_Equation2 (G : Type*) [Magma G] (h : Equation17218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0))) := superpose eq7 eq10
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq12
  have eq35 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq79 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq35 eq7
  have eq403 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq34 eq17
  have eq446 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq11 eq403
  have eq447 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq446
  have eq448 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq34 eq447
  have eq456 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq448 eq79
  have eq477 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq448 eq456
  have eq478 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq477 eq448
  have eq483 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq478 eq7
  have eq608 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq478 eq483
  have eq670 (X0 X2 : G) : X0 = X2 := superpose eq608 eq608
  have eq675 (X0 : G) : sK0 ≠ X0 := superpose eq670 eq8
  subsumption eq675 eq670


@[equational_result]
theorem Equation17220_implies_Equation2 (G : Type*) [Magma G] (h : Equation17220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq12 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 : G) : (((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) = X0 := superpose eq12 eq11
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq12 eq11
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq7 eq11
  have eq26 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X3) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) = X3 := superpose eq11 eq7
  have eq30 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq12 eq13
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq12 eq13
  have eq41 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0))) = X2 := superpose eq13 eq7
  have eq49 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X4 ◇ X3))) = X4 := superpose eq11 eq10
  have eq54 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1))))) = X3 := superpose eq11 eq10
  have eq55 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X4 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X0)))) = X4 := superpose eq10 eq10
  have eq71 (X0 X1 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq13 eq20
  have eq72 (X0 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) = X0 := superpose eq12 eq20
  have eq156 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq20 eq14
  have eq160 (X0 X1 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq14 eq11
  have eq171 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) = (X0 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0))) := superpose eq14 eq13
  have eq172 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0) = ((X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq14 eq20
  have eq200 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) = ((X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) := superpose eq17 eq11
  have eq212 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0))) = X0 := superpose eq17 eq20
  have eq226 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose eq34 eq7
  have eq235 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq34 eq20
  have eq237 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq226 eq235
  have eq238 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq30 eq237
  have eq324 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq238 eq7
  have eq345 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq12 eq324
  have eq414 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)))))) := superpose eq22 eq13
  have eq416 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = ((((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)))) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq22 eq20
  have eq430 (X0 : G) : ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose eq345 eq13
  have eq513 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)))) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X0)))) := superpose eq54 eq26
  have eq669 (X0 X1 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq17 eq55
  have eq854 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq34 eq41
  have eq911 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)))) := superpose eq41 eq26
  have eq1626 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq41 eq49
  have eq1704 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))))) = X0 := superpose eq12 eq1626
  have eq1709 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq156 eq1626
  have eq1730 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq1709 eq72
  have eq1749 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)))) = X0 := superpose eq1730 eq1704
  have eq1755 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq1749
  have eq1757 (X0 : G) : ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq1755 eq430
  have eq1759 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq345 eq1757
  have eq1763 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq1759 eq854
  have eq1765 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq1709 eq1763
  have eq1766 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1730 eq1765
  have eq1781 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) := superpose eq1766 eq160
  have eq1786 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0))) := superpose eq1766 eq171
  have eq1787 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0)) ◇ X0) := superpose eq1766 eq172
  have eq1801 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0)) = ((X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq1766 eq200
  have eq1809 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0))) = X0 := superpose eq1766 eq212
  have eq1853 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)))) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)))) ◇ X0))) := superpose eq1766 eq513
  have eq1881 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq1766 eq669
  have eq1908 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq1766 eq911
  have eq2205 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq1766 eq1781
  have eq2209 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) := superpose eq1766 eq1786
  have eq2210 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X0) := superpose eq1766 eq1787
  have eq2237 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = ((X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq1766 eq1801
  have eq2245 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X0 := superpose eq1766 eq1809
  have eq2246 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq2245 eq2237
  have eq2247 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := superpose eq2245 eq2246
  have eq2251 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq2247 eq2205
  have eq2252 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq1766 eq2251
  have eq2270 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq2252 eq2210
  have eq2279 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq2270 eq2209
  have eq2282 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq1766 eq2279
  have eq2283 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq1766 eq2282
  have eq2384 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)))) = (X0 ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)))) ◇ X0))) := superpose eq2252 eq1853
  have eq2385 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)))) = X0 := superpose eq2283 eq2384
  have eq2387 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq2385 eq414
  have eq2389 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq2385 eq416
  have eq2391 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0))) ◇ X0) := superpose eq2283 eq2389
  have eq2392 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0))) := superpose eq2391 eq2387
  have eq2440 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq1766 eq1881
  have eq2441 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X0 := superpose eq2252 eq2440
  have eq2509 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq2252 eq1908
  have eq2510 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq2283 eq2509
  have eq2512 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq2510 eq71
  have eq2518 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq2283 eq2512
  have eq2736 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq2518 eq20
  have eq2855 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq2518 eq2441
  have eq3094 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq2855 eq2392
  have eq3095 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq3094 eq13
  have eq3323 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq3095 eq2736
  have eq3336 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1766 eq3323
  have eq3337 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := superpose eq3336 eq7
  have eq3576 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq3336 eq3337
  have eq3655 (X0 X2 : G) : X0 = X2 := superpose eq3576 eq3576
  have eq3657 (X0 : G) : sK0 ≠ X0 := superpose eq3655 eq8
  subsumption eq3657 eq3655


@[equational_result]
theorem Equation17222_implies_Equation2 (G : Type*) [Magma G] (h : Equation17222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq36 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X1)) = X0 := superpose eq12 eq11
  have eq39 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq11 eq11
  have eq41 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) = (((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4))))) ◇ X0) := superpose eq7 eq11
  have eq83 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)))) := superpose eq9 eq9
  have eq95 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq36 eq83
  have eq107 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X4) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq9 eq36
  have eq125 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) = (X0 ◇ X0) := superpose eq107 eq41
  have eq127 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq125 eq95
  have eq133 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq11 eq127
  have eq166 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = X1 := superpose eq36 eq133
  have eq167 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq166 eq39
  have eq168 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq167 eq12
  have eq225 (X0 X1 : G) : X0 = X1 := superpose eq168 eq167
  have eq227 (X0 : G) : sK0 ≠ X0 := superpose eq225 eq8
  subsumption eq227 eq225


@[equational_result]
theorem Equation17225_implies_Equation2 (G : Type*) [Magma G] (h : Equation17225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq7 eq11
  have eq17 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))))) = X0 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose eq11 eq10
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq7 eq10
  have eq92 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq17
  have eq94 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq17 eq17
  have eq96 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq9 eq17
  have eq137 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq12 eq10
  have eq233 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq7 eq94
  have eq250 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq92 eq94
  have eq284 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X0 ◇ X1) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))) := superpose eq233 eq137
  have eq291 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X1 := superpose eq250 eq284
  have eq296 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ X1) := superpose eq291 eq96
  have eq321 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq296 eq17
  have eq355 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ X1)) := superpose eq296 eq20
  have eq406 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := superpose eq355 eq19
  have eq434 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq321 eq406
  have eq435 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq434 eq11
  have eq466 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq434 eq435
  have eq491 (X0 X2 : G) : X0 = X2 := superpose eq466 eq466
  have eq493 (X0 : G) : sK0 ≠ X0 := superpose eq491 eq8
  subsumption eq493 eq491


@[equational_result]
theorem Equation17228_implies_Equation2 (G : Type*) [Magma G] (h : Equation17228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X3)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0))) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) := superpose eq10 eq7
  have eq28 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X4)))) := superpose eq10 eq9
  have eq38 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2))))) = X3 := superpose eq9 eq7
  have eq43 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X4)) = ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq10
  have eq51 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X4)) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq18 eq43
  have eq52 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X2) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq10 eq51
  have eq53 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq52 eq10
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0))) := superpose eq52 eq12
  have eq59 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) = (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X4)))) := superpose eq52 eq28
  have eq68 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq52 eq38
  have eq74 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) := superpose eq52 eq55
  have eq77 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X4)))) := superpose eq52 eq59
  have eq91 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X3 := superpose eq52 eq68
  have eq117 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq53 eq91
  have eq128 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = X2 := superpose eq53 eq117
  have eq130 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq128
  have eq133 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq128 eq128
  have eq146 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X2 := superpose eq130 eq77
  have eq149 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq146 eq74
  have eq176 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq133 eq149
  have eq188 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := superpose eq176 eq7
  have eq207 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = X0 := superpose eq176 eq188
  have eq208 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq176 eq207
  have eq209 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq176 eq208
  have eq229 (X0 X1 : G) : X0 = X1 := superpose eq209 eq176
  have eq239 (X0 : G) : sK0 ≠ X0 := superpose eq229 eq8
  subsumption eq239 eq229


@[equational_result]
theorem Equation17230_implies_Equation2 (G : Type*) [Magma G] (h : Equation17230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X2 := superpose eq7 eq11
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = (X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))))) := superpose eq11 eq7
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq9
  have eq40 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X1)))) = ((X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) := superpose eq9 eq11
  have eq49 (X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X1)))) = (((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) := superpose eq18 eq40
  have eq50 (X1 X2 X4 : G) : (X2 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq11 eq49
  have eq76 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0)))) := superpose eq35 eq7
  have eq243 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq14
  have eq267 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ X0) := superpose eq7 eq243
  have eq292 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq267 eq7
  have eq293 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))))) = (X1 ◇ X1) := superpose eq267 eq9
  have eq306 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0)))) := superpose eq267 eq76
  have eq368 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq267 eq293
  have eq377 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq267 eq306
  have eq378 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq292 eq377
  have eq382 (X1 X2 X4 : G) : (X2 ◇ X1) = (X1 ◇ (X4 ◇ X1)) := superpose eq378 eq50
  have eq408 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq378 eq382
  have eq414 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq408 eq368
  have eq429 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq408 eq414
  have eq430 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq408 eq429
  have eq668 (X0 X2 : G) : X0 = X2 := superpose eq430 eq430
  have eq670 (X0 : G) : sK0 ≠ X0 := superpose eq668 eq8
  subsumption eq670 eq668


@[equational_result]
theorem Equation17231_implies_Equation2 (G : Type*) [Magma G] (h : Equation17231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X3)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X4 ◇ X4))))) := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X2 ◇ (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X1)))))) = X3 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = ((X1 ◇ (X1 ◇ (X3 ◇ X3))) ◇ (X0 ◇ (X0 ◇ (X4 ◇ X4)))) := superpose eq7 eq9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X3))) = ((X1 ◇ (X4 ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) ◇ (X5 ◇ X5)))) := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X3))) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)))))) := superpose eq9 eq9
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq9
  have eq46 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2))))) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) := superpose eq9 eq31
  have eq66 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X4))))) := superpose eq31 eq10
  have eq95 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq13
  have eq102 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq13
  have eq114 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4))))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X5 ◇ (X6 ◇ X6))))) := superpose eq13 eq10
  have eq124 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4))))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X5))) := superpose eq13 eq95
  have eq128 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X3))) = (X1 ◇ (X1 ◇ X2)) := superpose eq95 eq95
  have eq160 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X4 ◇ X4)) = ((X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X3 ◇ X3)))) ◇ (((X1 ◇ X1) ◇ X2) ◇ X2)) := superpose eq9 eq15
  have eq163 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (X0 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X0)) := superpose eq15 eq15
  have eq187 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X2) = (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X3))) := superpose eq15 eq95
  have eq199 (X1 X2 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X4 ◇ X4)) = ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (((X1 ◇ X1) ◇ X2) ◇ X2)) := superpose eq187 eq160
  have eq200 (X1 X2 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X4 ◇ X4)) = X2 := superpose eq15 eq199
  have eq202 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X0)) := superpose eq200 eq163
  have eq204 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X3))) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)))) := superpose eq200 eq29
  have eq205 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) = ((X1 ◇ X1) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) := superpose eq200 eq46
  have eq215 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X3)) = X2 := superpose eq15 eq200
  have eq273 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq215 eq202
  have eq275 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) = ((X1 ◇ X1) ◇ X1) := superpose eq215 eq205
  have eq283 (X0 X1 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X3 ◇ X3))) ◇ (X0 ◇ (X0 ◇ (X4 ◇ X4)))) = ((X1 ◇ X0) ◇ X0) := superpose eq215 eq23
  have eq285 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X3))) = ((X1 ◇ (X4 ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ X5)))) := superpose eq215 eq25
  have eq301 (X1 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X3))) = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq275 eq204
  have eq302 (X1 X3 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X3 ◇ X3))) := superpose eq273 eq301
  have eq304 (X0 X1 X3 X4 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X4 ◇ X4))))) := superpose eq302 eq11
  have eq309 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X4))))) := superpose eq302 eq66
  have eq320 (X1 X2 X3 X4 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4))))) := superpose eq304 eq114
  have eq324 (X0 X1 X5 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X5))) := superpose eq320 eq124
  have eq329 (X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ X2)) := superpose eq324 eq128
  have eq343 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq329 eq309
  have eq344 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq215 eq343
  have eq375 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X0)) := superpose eq329 eq283
  have eq376 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq329 eq375
  have eq377 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq215 eq376
  have eq384 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq377 eq102
  have eq389 (X0 X1 X3 X4 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X3))) = ((X1 ◇ (X4 ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq329 eq285
  have eq390 (X0 X1 X3 X4 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X3))) = ((X1 ◇ (X4 ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq377 eq389
  have eq391 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X3))) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq344 eq390
  have eq392 (X1 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X3))) = X1 := superpose eq344 eq391
  have eq393 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq344 eq392
  have eq394 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X4 ◇ X4)) = X2 := superpose eq393 eq200
  have eq407 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X4) = X2 := superpose eq393 eq394
  have eq408 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq407 eq384
  have eq409 (X0 X1 : G) : X0 = X1 := superpose eq393 eq408
  have eq420 (X0 : G) : sK0 ≠ X0 := superpose eq409 eq8
  subsumption eq420 eq409


@[equational_result]
theorem Equation17232_implies_Equation2 (G : Type*) [Magma G] (h : Equation17232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq10 eq11
  have eq27 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq11 eq11
  have eq43 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq20 eq20
  have eq46 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq11 eq20
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq20 eq11
  have eq63 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X3)) := superpose eq20 eq11
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X1 := superpose eq11 eq46
  have eq65 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq64 eq27
  have eq73 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2))) := superpose eq63 eq43
  have eq74 (X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = X2 := superpose eq65 eq73
  have eq76 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq74 eq20
  have eq99 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq76 eq56
  have eq104 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X2 := superpose eq64 eq99
  have eq109 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq104 eq76
  have eq129 (X0 X2 : G) : X0 = X2 := superpose eq109 eq109
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq131 eq129


@[equational_result]
theorem Equation17234_implies_Equation2 (G : Type*) [Magma G] (h : Equation17234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq7 eq12
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq12
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq12 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X0))) := superpose eq17 eq10
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq7 eq18
  have eq68 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq13 eq52
  have eq69 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq17 eq68
  have eq73 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq69 eq12
  have eq109 (X0 X1 : G) : X0 = X1 := superpose eq14 eq73
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq109 eq8
  subsumption eq123 eq109


@[equational_result]
theorem Equation17236_implies_Equation2 (G : Type*) [Magma G] (h : Equation17236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq23 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq36 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq23 eq12
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq11 eq36
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq96 eq39


@[equational_result]
theorem Equation17238_implies_Equation2 (G : Type*) [Magma G] (h : Equation17238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))))) = X1 := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq7
  have eq20 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq13 eq7
  have eq22 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose eq13 eq15
  have eq24 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq16 eq22
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq20 eq24
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq66 eq30


@[equational_result]
theorem Equation17240_implies_Equation2 (G : Type*) [Magma G] (h : Equation17240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq23 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq36 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq23 eq12
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq11 eq36
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq95 eq40


@[equational_result]
theorem Equation17243_implies_Equation2 (G : Type*) [Magma G] (h : Equation17243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq34 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0) ◇ X3) ◇ X0) = X3 := superpose eq7 eq10
  have eq89 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X4) = X5 := superpose eq34 eq34
  have eq109 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) ◇ X0) ◇ ((X4 ◇ (X5 ◇ (X5 ◇ X5))) ◇ (X5 ◇ (X5 ◇ X5))))) = X3 := superpose eq34 eq10
  have eq125 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X3 := superpose eq7 eq89
  have eq172 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq125 eq109
  have eq270 (X0 X2 : G) : X0 = X2 := superpose eq172 eq172
  have eq356 (X0 : G) : sK0 ≠ X0 := superpose eq270 eq8
  subsumption eq356 eq270


@[equational_result]
theorem Equation17244_implies_Equation2 (G : Type*) [Magma G] (h : Equation17244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq11 eq11
  have eq21 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq13 eq11
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq35 eq24


@[equational_result]
theorem Equation17246_implies_Equation2 (G : Type*) [Magma G] (h : Equation17246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ X0) := superpose eq7 eq12
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X1) ◇ X0))))) = X1 := superpose eq12 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq12 eq7
  have eq22 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq14 eq7
  have eq24 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose eq14 eq17
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq18 eq24
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq22 eq26
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq68 eq32


@[equational_result]
theorem Equation17247_implies_Equation2 (G : Type*) [Magma G] (h : Equation17247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq28 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq12 eq12
  have eq39 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq28 eq17
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq39 eq39
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq108 eq48


@[equational_result]
theorem Equation17248_implies_Equation2 (G : Type*) [Magma G] (h : Equation17248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq23 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq35 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq23 eq12
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq11 eq35
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq100 eq39


@[equational_result]
theorem Equation17249_implies_Equation2 (G : Type*) [Magma G] (h : Equation17249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq23 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq36 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq23 eq12
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq11 eq36
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq83 eq40


@[equational_result]
theorem Equation17251_implies_Equation2 (G : Type*) [Magma G] (h : Equation17251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X0)) ◇ (X3 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq12 eq7
  have eq48 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq17 eq7
  have eq51 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq17 eq11
  have eq57 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq48 eq10
  have eq68 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq17 eq57
  have eq102 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq48
  have eq107 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq48 eq11
  have eq121 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq102 eq107
  have eq122 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq121 eq68
  have eq131 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq121 eq122
  have eq133 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq131 eq51
  have eq181 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq131 eq133
  have eq182 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq131 eq181
  have eq183 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq131 eq182
  have eq186 (X0 X1 : G) : X0 = X1 := superpose eq131 eq183
  have eq196 (X0 : G) : sK0 ≠ X0 := superpose eq186 eq8
  subsumption eq196 eq186


@[equational_result]
theorem Equation17252_implies_Equation2 (G : Type*) [Magma G] (h : Equation17252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) := superpose eq7 eq12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq17 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := superpose eq12 eq7
  have eq20 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq17 eq14
  have eq43 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq12 eq20
  have eq48 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq12 eq43
  have eq49 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq15 eq48
  have eq53 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X0 := superpose eq49 eq20
  have eq54 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq49 eq53
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq54 eq54
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq64 eq59


@[equational_result]
theorem Equation17253_implies_Equation2 (G : Type*) [Magma G] (h : Equation17253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) := superpose eq7 eq12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq17 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := superpose eq12 eq7
  have eq20 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq17 eq14
  have eq25 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X0)) = X0 := superpose eq12 eq11
  have eq27 (X0 X1 X2 X4 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X4 ◇ X1)) := superpose eq11 eq11
  have eq32 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq25 eq27
  have eq35 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq32 eq20
  have eq39 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq32 eq35
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq15 eq39
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq48 eq40


@[equational_result]
theorem Equation17255_implies_Equation2 (G : Type*) [Magma G] (h : Equation17255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X3 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq11
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq10 eq7
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq27 eq13
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := superpose eq29 eq9
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq29 eq12
  have eq48 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)))) := superpose eq29 eq31
  have eq49 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq29 eq34
  have eq50 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) := superpose eq49 eq48
  have eq54 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq49 eq50
  have eq55 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq49 eq54
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq49 eq55
  have eq57 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq29 eq56
  have eq87 (X0 X1 : G) : X0 = X1 := superpose eq57 eq49
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq100 eq87


@[equational_result]
theorem Equation17257_implies_Equation2 (G : Type*) [Magma G] (h : Equation17257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq12 eq7
  have eq25 (X0 X1 X2 X4 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X4 ◇ X1)) := superpose eq11 eq11
  have eq30 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq18 eq25
  have eq32 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq30 eq12
  have eq38 (X0 X1 : G) : X0 = X1 := superpose eq32 eq30
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation17261_implies_Equation2 (G : Type*) [Magma G] (h : Equation17261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq7 eq7
  have eq26 (X0 X1 X2 X4 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X4 ◇ X1)) := superpose eq11 eq11
  have eq28 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) = ((X4 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) ◇ X0) := superpose eq10 eq11
  have eq48 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X1)) = ((X4 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq11 eq26
  have eq76 (X1 X2 X3 : G) : (X3 ◇ X1) = (X2 ◇ (X3 ◇ X1)) := superpose eq11 eq48
  have eq83 (X0 X1 X3 X4 : G) : (X1 ◇ (X0 ◇ X3)) = ((X4 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq76 eq28
  have eq90 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := superpose eq76 eq7
  have eq111 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = ((X1 ◇ (X0 ◇ X3)) ◇ X0) := superpose eq76 eq83
  have eq112 (X0 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ X0) := superpose eq76 eq111
  have eq120 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = X0 := superpose eq76 eq90
  have eq121 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq120 eq26
  have eq124 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq121 eq112
  have eq131 (X0 X1 : G) : X0 = X1 := superpose eq121 eq124
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq141 eq131


@[equational_result]
theorem Equation17263_implies_Equation2 (G : Type*) [Magma G] (h : Equation17263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation17264_implies_Equation2 (G : Type*) [Magma G] (h : Equation17264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq12 eq7
  have eq24 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X0)) = X0 := superpose eq12 eq11
  have eq26 (X0 X1 X2 X3 X5 X6 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X5 ◇ X6)) ◇ X1)) := superpose eq11 eq11
  have eq27 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X1)) := superpose eq12 eq11
  have eq35 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X1) = X1 := superpose eq24 eq26
  have eq40 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq35 eq27
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq12 eq40
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq41 eq15
  have eq48 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq14 eq43
  have eq49 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq41 eq48
  have eq65 (X0 X1 : G) : X0 = X1 := superpose eq41 eq49
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq78 eq65


@[equational_result]
theorem Equation17265_implies_Equation2 (G : Type*) [Magma G] (h : Equation17265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X1 X2 X4 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X4 ◇ X1)) := superpose eq10 eq10
  have eq32 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq15 eq28
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq32 eq11
  have eq39 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq32 eq33
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq39 eq32
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation17266_implies_Equation2 (G : Type*) [Magma G] (h : Equation17266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq34 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq90 eq34


@[equational_result]
theorem Equation17268_implies_Equation2 (G : Type*) [Magma G] (h : Equation17268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq7
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq17 eq11
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq21 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq21 eq25
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation17270_implies_Equation2 (G : Type*) [Magma G] (h : Equation17270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X2 := superpose eq12 eq11
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq12 eq13
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq42 eq26


@[equational_result]
theorem Equation17272_implies_Equation2 (G : Type*) [Magma G] (h : Equation17272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq7
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = X1 := superpose eq19 eq11
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq50 eq40


@[equational_result]
theorem Equation17273_implies_Equation2 (G : Type*) [Magma G] (h : Equation17273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq12
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq12
  have eq17 (X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X2))) = X1 := superpose eq14 eq13
  have eq36 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) = X1 := superpose eq12 eq11
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X0)) := superpose eq11 eq11
  have eq47 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2) := superpose eq36 eq37
  have eq62 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq17 eq12
  have eq68 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq62 eq47
  have eq71 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq62 eq68
  have eq75 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq71
  have eq82 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq75 eq12
  have eq87 (X0 X2 : G) : X0 = X2 := superpose eq82 eq82
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq89 eq87


@[equational_result]
theorem Equation17274_implies_Equation2 (G : Type*) [Magma G] (h : Equation17274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X2 := superpose eq12 eq11
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq44 eq27


@[equational_result]
theorem Equation17276_implies_Equation2 (G : Type*) [Magma G] (h : Equation17276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X2 ◇ X1))) = (X0 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq20 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq17
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X3))) = ((X4 ◇ ((X1 ◇ X3) ◇ (X4 ◇ (X1 ◇ X3)))) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq9 eq9
  have eq61 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq7 eq20
  have eq75 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X2 ◇ X1))) = (X0 ◇ (X1 ◇ X0)) := superpose eq61 eq9
  have eq80 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X3))) = ((X1 ◇ X3) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := superpose eq61 eq30
  have eq99 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X3))) = ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq61 eq80
  have eq100 (X2 X3 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X3))) = X3 := superpose eq7 eq99
  have eq112 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq100 eq75
  have eq124 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq112 eq100
  have eq156 (X0 X2 : G) : X0 = X2 := superpose eq124 eq124
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq156 eq8
  subsumption eq158 eq156


@[equational_result]
theorem Equation17278_implies_Equation2 (G : Type*) [Magma G] (h : Equation17278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq10
  have eq43 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X2 := superpose eq32 eq11
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq64 eq53


@[equational_result]
theorem Equation17280_implies_Equation2 (G : Type*) [Magma G] (h : Equation17280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq12
  have eq22 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation17281_implies_Equation2 (G : Type*) [Magma G] (h : Equation17281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ (X5 ◇ X3))) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X2))) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq12
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq12
  have eq18 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X2))) = X1 := superpose eq14 eq13
  have eq19 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X4 ◇ (X1 ◇ X0))) = X2 := superpose eq18 eq10
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) = X1 := superpose eq12 eq19
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X1 ◇ X3)) = (X0 ◇ (X4 ◇ ((X1 ◇ X0) ◇ X5))) := superpose eq19 eq19
  have eq31 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = X1 := superpose eq24 eq25
  have eq33 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq31 eq18
  have eq36 (X0 X2 : G) : X0 = X2 := superpose eq12 eq33
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq49 eq36


@[equational_result]
theorem Equation17282_implies_Equation2 (G : Type*) [Magma G] (h : Equation17282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X2 := superpose eq12 eq11
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq12 eq13
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq42 eq26


@[equational_result]
theorem Equation17283_implies_Equation2 (G : Type*) [Magma G] (h : Equation17283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X2 := superpose eq12 eq11
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq43 eq26


@[equational_result]
theorem Equation17287_implies_Equation2 (G : Type*) [Magma G] (h : Equation17287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X3 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ X2) := superpose eq11 eq12
  have eq45 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X4))) = X2 := superpose eq19 eq11
  have eq56 (X0 X1 X2 X4 : G) : (X2 ◇ (X2 ◇ X1)) = ((X0 ◇ X1) ◇ (X4 ◇ (X4 ◇ (X2 ◇ X1)))) := superpose eq10 eq10
  have eq77 (X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = X1 := superpose eq45 eq56
  have eq79 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X4) = X2 := superpose eq77 eq45
  have eq91 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq79 eq26
  have eq96 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq91 eq19
  have eq101 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq91 eq96
  have eq104 (X0 X1 : G) : X0 = X1 := superpose eq91 eq101
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq104 eq8
  subsumption eq106 eq104


@[equational_result]
theorem Equation17290_implies_Equation2 (G : Type*) [Magma G] (h : Equation17290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X2))) = (X0 ◇ (X3 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X3)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ (X3 ◇ (X1 ◇ X3))) ◇ ((X3 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq11 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (X0 ◇ ((X3 ◇ (X3 ◇ (X2 ◇ X3))) ◇ ((X3 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X0))) := superpose eq7 eq9
  have eq33 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq9
  have eq36 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq9
  have eq37 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))))) = X3 := superpose eq9 eq7
  have eq45 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq15
  have eq56 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq45 eq11
  have eq80 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) = (X3 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X3))) := superpose eq7 eq36
  have eq105 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X3 ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq36 eq7
  have eq110 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ X2) ◇ X2)) = ((X2 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq36 eq15
  have eq137 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ ((X2 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) ◇ ((X2 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) ◇ X0))) := superpose eq15 eq10
  have eq168 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) := superpose eq10 eq36
  have eq191 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) = ((X2 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq36 eq33
  have eq197 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq10 eq33
  have eq202 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))))) = (X1 ◇ (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1))) := superpose eq10 eq33
  have eq235 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) := superpose eq33 eq56
  have eq236 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq197
  have eq237 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq191 eq236
  have eq242 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1))) := superpose eq168 eq202
  have eq243 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1))) := superpose eq237 eq242
  have eq269 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0)))) = X2 := superpose eq56 eq37
  have eq280 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq10 eq37
  have eq313 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose eq237 eq280
  have eq314 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq56 eq313
  have eq315 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq314 eq45
  have eq317 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq314 eq235
  have eq351 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq315 eq237
  have eq354 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1))) := superpose eq315 eq243
  have eq358 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)))) = X2 := superpose eq315 eq269
  have eq389 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := superpose eq105 eq317
  have eq402 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq389 eq110
  have eq404 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X2 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) ◇ ((X2 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) ◇ X0))) := superpose eq389 eq137
  have eq433 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq402 eq351
  have eq434 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X1))) := superpose eq402 eq354
  have eq440 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq433
  have eq441 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq7 eq434
  have eq442 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq314 eq441
  have eq444 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq442 eq404
  have eq445 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) = X2 := superpose eq444 eq358
  have eq447 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq445 eq440
  have eq451 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2)))) = ((X1 ◇ X1) ◇ X1) := superpose eq447 eq17
  have eq504 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq447 eq451
  have eq505 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2)))) = X1 := superpose eq447 eq504
  have eq506 (X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X2))) = X1 := superpose eq505 eq9
  have eq533 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq506 eq7
  have eq537 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X3 ◇ (X2 ◇ X3))) ◇ ((X3 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X0))) = X2 := superpose eq506 eq29
  have eq539 (X0 X2 X3 : G) : (X3 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X3))) = (X2 ◇ (X2 ◇ X0)) := superpose eq506 eq80
  have eq575 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq506 eq537
  have eq576 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X2 ◇ X0)) := superpose eq506 eq539
  have eq577 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq576 eq575
  have eq581 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq577 eq506
  have eq584 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq581 eq533
  have eq715 (X0 X1 : G) : X0 = X1 := superpose eq584 eq581
  have eq717 (X0 : G) : sK0 ≠ X0 := superpose eq715 eq8
  subsumption eq717 eq715


@[equational_result]
theorem Equation17291_implies_Equation2 (G : Type*) [Magma G] (h : Equation17291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq21 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq14 eq12
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq37 eq26


@[equational_result]
theorem Equation17294_implies_Equation2 (G : Type*) [Magma G] (h : Equation17294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X2))) = (X0 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3)))) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq9
  have eq36 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq57 eq36


@[equational_result]
theorem Equation17295_implies_Equation2 (G : Type*) [Magma G] (h : Equation17295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq159 eq63


@[equational_result]
theorem Equation17297_implies_Equation2 (G : Type*) [Magma G] (h : Equation17297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq12
  have eq22 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq37 eq24


@[equational_result]
theorem Equation17298_implies_Equation2 (G : Type*) [Magma G] (h : Equation17298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (X2 ◇ (X3 ◇ X2))) = (X0 ◇ (X4 ◇ (X4 ◇ (X5 ◇ X4)))) := superpose eq7 eq7
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := superpose eq7 eq9
  have eq79 (X0 X3 : G) : X0 = X3 := superpose eq40 eq40
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq106 eq79


@[equational_result]
theorem Equation17299_implies_Equation2 (G : Type*) [Magma G] (h : Equation17299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq131 eq35


@[equational_result]
theorem Equation17300_implies_Equation2 (G : Type*) [Magma G] (h : Equation17300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq34 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq134 eq34


@[equational_result]
theorem Equation17302_implies_Equation2 (G : Type*) [Magma G] (h : Equation17302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq12 eq12
  have eq18 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))))) = X1 := superpose eq12 eq7
  have eq31 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq16 eq18
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq12 eq31
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq76 eq44


@[equational_result]
theorem Equation17303_implies_Equation2 (G : Type*) [Magma G] (h : Equation17303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq146 eq56


@[equational_result]
theorem Equation17304_implies_Equation2 (G : Type*) [Magma G] (h : Equation17304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq145 eq55


@[equational_result]
theorem Equation17305_implies_Equation2 (G : Type*) [Magma G] (h : Equation17305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq31 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq90 eq31


@[equational_result]
theorem Equation17307_implies_Equation2 (G : Type*) [Magma G] (h : Equation17307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq12
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq39 eq26


@[equational_result]
theorem Equation17308_implies_Equation2 (G : Type*) [Magma G] (h : Equation17308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ (X4 ◇ (X1 ◇ X3))) ◇ (X5 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X3 ◇ (X4 ◇ (X1 ◇ X3))) ◇ (X5 ◇ X0))) = X2 := superpose eq12 eq10
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ X3))) = X2 := superpose eq12 eq13
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq49 eq31


@[equational_result]
theorem Equation17309_implies_Equation2 (G : Type*) [Magma G] (h : Equation17309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq113 eq36


@[equational_result]
theorem Equation17310_implies_Equation2 (G : Type*) [Magma G] (h : Equation17310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq32 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq100 eq32


@[equational_result]
theorem Equation17312_implies_Equation2 (G : Type*) [Magma G] (h : Equation17312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq37 eq24


@[equational_result]
theorem Equation17313_implies_Equation2 (G : Type*) [Magma G] (h : Equation17313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq142 eq53


@[equational_result]
theorem Equation17314_implies_Equation2 (G : Type*) [Magma G] (h : Equation17314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X3))) = (X0 ◇ (X4 ◇ (X5 ◇ (X4 ◇ X5)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq42 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq9
  have eq98 (X0 X2 : G) : X0 = X2 := superpose eq11 eq42
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq134 eq98


@[equational_result]
theorem Equation17315_implies_Equation2 (G : Type*) [Magma G] (h : Equation17315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq10
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq31 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq127 eq31


@[equational_result]
theorem Equation17317_implies_Equation2 (G : Type*) [Magma G] (h : Equation17317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq12
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq37 eq24


@[equational_result]
theorem Equation17318_implies_Equation2 (G : Type*) [Magma G] (h : Equation17318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq159 eq63


@[equational_result]
theorem Equation17319_implies_Equation2 (G : Type*) [Magma G] (h : Equation17319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ (X3 ◇ X3))) = (X0 ◇ (X4 ◇ (X5 ◇ (X5 ◇ X5)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq9
  have eq97 (X0 X3 : G) : X0 = X3 := superpose eq11 eq41
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq132 eq97


@[equational_result]
theorem Equation17320_implies_Equation2 (G : Type*) [Magma G] (h : Equation17320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq31 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq127 eq31


@[equational_result]
theorem Equation17322_implies_Equation2 (G : Type*) [Magma G] (h : Equation17322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq7 eq21
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq37 eq24


@[equational_result]
theorem Equation17323_implies_Equation2 (G : Type*) [Magma G] (h : Equation17323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq63 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq159 eq63


@[equational_result]
theorem Equation17324_implies_Equation2 (G : Type*) [Magma G] (h : Equation17324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq34 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq134 eq34


@[equational_result]
theorem Equation17325_implies_Equation2 (G : Type*) [Magma G] (h : Equation17325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq30 (X0 X5 : G) : X0 = X5 := superpose eq7 eq14
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq95 eq30


@[equational_result]
theorem Equation17326_implies_Equation2 (G : Type*) [Magma G] (h : Equation17326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq30 (X0 X6 : G) : X0 = X6 := superpose eq7 eq14
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq83 eq30


@[equational_result]
theorem Equation17329_implies_Equation2 (G : Type*) [Magma G] (h : Equation17329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq7 eq9
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X0) := superpose eq7 eq20
  have eq53 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq34
  have eq81 (X0 X2 : G) : X0 = X2 := superpose eq53 eq53
  have eq178 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq178 eq81


@[equational_result]
theorem Equation17332_implies_Equation2 (G : Type*) [Magma G] (h : Equation17332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = X1 := superpose eq10 eq9
  have eq214 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq21 eq14
  have eq227 (X0 X2 : G) : X0 = X2 := superpose eq214 eq214
  have eq367 (X0 : G) : sK0 ≠ X0 := superpose eq227 eq8
  subsumption eq367 eq227


@[equational_result]
theorem Equation17334_implies_Equation2 (G : Type*) [Magma G] (h : Equation17334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq11 eq7
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq14
  have eq23 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((((X0 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1))) ◇ X0) := superpose eq7 eq10
  have eq26 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq10
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq26 eq16
  have eq48 (X0 X1 X3 : G) : (X1 ◇ X1) = (((X3 ◇ X1) ◇ (X3 ◇ X1)) ◇ X0) := superpose eq35 eq23
  have eq61 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq35 eq48
  have eq65 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq61
  have eq84 (X0 X2 : G) : X0 = X2 := superpose eq65 eq65
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq117 eq84


@[equational_result]
theorem Equation17336_implies_Equation2 (G : Type*) [Magma G] (h : Equation17336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq7 eq7
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ X0) := superpose eq7 eq10
  have eq55 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq32
  have eq91 (X0 X2 : G) : X0 = X2 := superpose eq55 eq55
  have eq205 (X0 : G) : sK0 ≠ X0 := superpose eq91 eq8
  subsumption eq205 eq91


@[equational_result]
theorem Equation17339_implies_Equation2 (G : Type*) [Magma G] (h : Equation17339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq10 eq10
  have eq18 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq10
  have eq22 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq18 eq18
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq18 eq7
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq22 eq18
  have eq42 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq31 eq26
  have eq63 (X0 X2 : G) : X0 = X2 := superpose eq18 eq42
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq101 eq63


@[equational_result]
theorem Equation17342_implies_Equation2 (G : Type*) [Magma G] (h : Equation17342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq11 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq13
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq10
  have eq24 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq17
  have eq25 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq24
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq25 eq14
  have eq27 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq26 eq25
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) = X2 := superpose eq27 eq9
  have eq41 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq31 eq31
  have eq48 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose eq31 eq26
  have eq49 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq41 eq27
  have eq50 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq49 eq41
  have eq57 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq49 eq48
  have eq58 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq49 eq57
  have eq59 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq58 eq50
  have eq60 (X0 X1 : G) : X0 = X1 := superpose eq59 eq58
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq78 eq60


@[equational_result]
theorem Equation17344_implies_Equation2 (G : Type*) [Magma G] (h : Equation17344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq13 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq10 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq10 eq12
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq15 eq10
  have eq20 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq15 eq13
  have eq21 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq20
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0) := superpose eq7 eq17
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) = (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) := superpose eq15 eq24
  have eq30 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq21 eq29
  have eq37 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq30
  have eq82 (X0 X2 : G) : X0 = X2 := superpose eq37 eq37
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq133 eq82


@[equational_result]
theorem Equation17345_implies_Equation2 (G : Type*) [Magma G] (h : Equation17345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq10 eq7
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) = X2 := superpose eq10 eq9
  have eq200 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ X0) := superpose eq23 eq23
  have eq310 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq15 eq200
  have eq449 (X0 X2 : G) : X0 = X2 := superpose eq310 eq310
  have eq640 (X0 : G) : sK0 ≠ X0 := superpose eq449 eq8
  subsumption eq640 eq449


@[equational_result]
theorem Equation17346_implies_Equation2 (G : Type*) [Magma G] (h : Equation17346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq73 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq11 eq10
  have eq99 (X0 X2 : G) : X0 = X2 := superpose eq73 eq73
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq130 eq99


@[equational_result]
theorem Equation17348_implies_Equation2 (G : Type*) [Magma G] (h : Equation17348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq11 eq7
  have eq21 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq10
  have eq23 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) = X1 := superpose eq11 eq10
  have eq30 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq21 eq23
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq30 eq15
  have eq78 (X0 X3 : G) : X0 = X3 := superpose eq33 eq33
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq100 eq78


@[equational_result]
theorem Equation17350_implies_Equation2 (G : Type*) [Magma G] (h : Equation17350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq24 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq42 (X0 X1 : G) : X0 = X1 := superpose eq10 eq24
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq107 eq42


@[equational_result]
theorem Equation17352_implies_Equation2 (G : Type*) [Magma G] (h : Equation17352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq92 eq37


@[equational_result]
theorem Equation17354_implies_Equation2 (G : Type*) [Magma G] (h : Equation17354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq10 eq9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq12 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17357_implies_Equation2 (G : Type*) [Magma G] (h : Equation17357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X1 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (X2 ◇ X2))))) = X1 := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq7 eq10
  have eq55 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ (X3 ◇ (((X4 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X4 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) ◇ (X4 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))))) = X3 := superpose eq21 eq10
  have eq81 (X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ (X3 ◇ (((X4 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X4 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X1 ◇ (X1 ◇ X1)))))) = X3 := superpose eq7 eq55
  have eq82 (X2 X3 X4 : G) : ((X2 ◇ X2) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq81
  have eq84 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X1 := superpose eq82 eq11
  have eq86 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (X2 ◇ X2))))) = X1 := superpose eq82 eq17
  have eq93 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2)))) = X1 := superpose eq84 eq86
  have eq95 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X0)))) = X2 := superpose eq21 eq84
  have eq116 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq82 eq95
  have eq122 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq116 eq93
  have eq130 (X0 X3 : G) : X0 = X3 := superpose eq122 eq122
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq130 eq8
  subsumption eq132 eq130


@[equational_result]
theorem Equation17358_implies_Equation2 (G : Type*) [Magma G] (h : Equation17358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq124 eq55


@[equational_result]
theorem Equation17360_implies_Equation2 (G : Type*) [Magma G] (h : Equation17360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) = X3 := superpose eq10 eq10
  have eq42 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq27 eq9
  have eq43 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X4 := superpose eq27 eq10
  have eq50 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq43 eq42
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq50 eq50
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq61 eq53


@[equational_result]
theorem Equation17361_implies_Equation2 (G : Type*) [Magma G] (h : Equation17361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq21 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq146 eq65


@[equational_result]
theorem Equation17362_implies_Equation2 (G : Type*) [Magma G] (h : Equation17362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq9 eq19
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq143 eq65


@[equational_result]
theorem Equation17363_implies_Equation2 (G : Type*) [Magma G] (h : Equation17363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X6)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq11 eq11
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X4) = X3 := superpose eq14 eq9
  have eq25 (X1 X3 X4 : G) : (X1 ◇ X4) = X3 := superpose eq14 eq21
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq11 eq25
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq35 eq26


@[equational_result]
theorem Equation17366_implies_Equation2 (G : Type*) [Magma G] (h : Equation17366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq15
  have eq19 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := superpose eq7 eq10
  have eq24 (X0 X1 : G) : (X1 ◇ X1) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0) := superpose eq7 eq10
  have eq32 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq19 eq24
  have eq37 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq32 eq16
  have eq41 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq37 eq11
  have eq43 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq41 eq10
  have eq46 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq41 eq32
  have eq51 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq41 eq43
  have eq52 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq46 eq51
  have eq61 (X0 X2 : G) : X0 = X2 := superpose eq52 eq52
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq66 eq61


@[equational_result]
theorem Equation17369_implies_Equation2 (G : Type*) [Magma G] (h : Equation17369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq11
  have eq19 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq10
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq10 eq19
  have eq37 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq20 eq7
  have eq40 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq20 eq31
  have eq43 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq40 eq37
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq43 eq43
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq53 eq51


@[equational_result]
theorem Equation17371_implies_Equation2 (G : Type*) [Magma G] (h : Equation17371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq34 eq14


@[equational_result]
theorem Equation17372_implies_Equation2 (G : Type*) [Magma G] (h : Equation17372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq34 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) = X1 := superpose eq12 eq10
  have eq40 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq10 eq34
  have eq41 (X0 X2 : G) : X0 = X2 := superpose eq7 eq40
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq142 eq41


@[equational_result]
theorem Equation17373_implies_Equation2 (G : Type*) [Magma G] (h : Equation17373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq35
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq123 eq57


@[equational_result]
theorem Equation17376_implies_Equation2 (G : Type*) [Magma G] (h : Equation17376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq44 eq32


@[equational_result]
theorem Equation17378_implies_Equation2 (G : Type*) [Magma G] (h : Equation17378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation17379_implies_Equation2 (G : Type*) [Magma G] (h : Equation17379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17381_implies_Equation2 (G : Type*) [Magma G] (h : Equation17381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17382_implies_Equation2 (G : Type*) [Magma G] (h : Equation17382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation17383_implies_Equation2 (G : Type*) [Magma G] (h : Equation17383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17385_implies_Equation2 (G : Type*) [Magma G] (h : Equation17385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq37 eq14


@[equational_result]
theorem Equation17387_implies_Equation2 (G : Type*) [Magma G] (h : Equation17387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation17389_implies_Equation2 (G : Type*) [Magma G] (h : Equation17389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation17390_implies_Equation2 (G : Type*) [Magma G] (h : Equation17390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17391_implies_Equation2 (G : Type*) [Magma G] (h : Equation17391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17393_implies_Equation2 (G : Type*) [Magma G] (h : Equation17393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17394_implies_Equation2 (G : Type*) [Magma G] (h : Equation17394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17395_implies_Equation2 (G : Type*) [Magma G] (h : Equation17395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17397_implies_Equation2 (G : Type*) [Magma G] (h : Equation17397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17398_implies_Equation2 (G : Type*) [Magma G] (h : Equation17398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17399_implies_Equation2 (G : Type*) [Magma G] (h : Equation17399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17400_implies_Equation2 (G : Type*) [Magma G] (h : Equation17400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17402_implies_Equation2 (G : Type*) [Magma G] (h : Equation17402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X0)) := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X2 := superpose eq10 eq7
  have eq108 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq108 eq8
  subsumption eq127 eq108


@[equational_result]
theorem Equation17404_implies_Equation2 (G : Type*) [Magma G] (h : Equation17404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq12
  have eq22 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X4))) = X3 := superpose eq14 eq9
  have eq26 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq14 eq22
  have eq27 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq14 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation17406_implies_Equation2 (G : Type*) [Magma G] (h : Equation17406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq36 eq13


@[equational_result]
theorem Equation17407_implies_Equation2 (G : Type*) [Magma G] (h : Equation17407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq46 eq13


@[equational_result]
theorem Equation17408_implies_Equation2 (G : Type*) [Magma G] (h : Equation17408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq51 eq13


@[equational_result]
theorem Equation17411_implies_Equation2 (G : Type*) [Magma G] (h : Equation17411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = X0 := superpose eq10 eq7
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq33 eq24


@[equational_result]
theorem Equation17412_implies_Equation2 (G : Type*) [Magma G] (h : Equation17412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation17414_implies_Equation2 (G : Type*) [Magma G] (h : Equation17414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation17415_implies_Equation2 (G : Type*) [Magma G] (h : Equation17415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation17416_implies_Equation2 (G : Type*) [Magma G] (h : Equation17416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation17417_implies_Equation2 (G : Type*) [Magma G] (h : Equation17417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation17419_implies_Equation2 (G : Type*) [Magma G] (h : Equation17419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq10 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq83 eq30


@[equational_result]
theorem Equation17421_implies_Equation2 (G : Type*) [Magma G] (h : Equation17421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq58 eq14


@[equational_result]
theorem Equation17423_implies_Equation2 (G : Type*) [Magma G] (h : Equation17423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation17424_implies_Equation2 (G : Type*) [Magma G] (h : Equation17424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17425_implies_Equation2 (G : Type*) [Magma G] (h : Equation17425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17427_implies_Equation2 (G : Type*) [Magma G] (h : Equation17427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17428_implies_Equation2 (G : Type*) [Magma G] (h : Equation17428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation17429_implies_Equation2 (G : Type*) [Magma G] (h : Equation17429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17431_implies_Equation2 (G : Type*) [Magma G] (h : Equation17431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17432_implies_Equation2 (G : Type*) [Magma G] (h : Equation17432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17433_implies_Equation2 (G : Type*) [Magma G] (h : Equation17433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17434_implies_Equation2 (G : Type*) [Magma G] (h : Equation17434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17438_implies_Equation2 (G : Type*) [Magma G] (h : Equation17438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq61 eq40


@[equational_result]
theorem Equation17440_implies_Equation2 (G : Type*) [Magma G] (h : Equation17440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation17441_implies_Equation2 (G : Type*) [Magma G] (h : Equation17441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17442_implies_Equation2 (G : Type*) [Magma G] (h : Equation17442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17444_implies_Equation2 (G : Type*) [Magma G] (h : Equation17444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17445_implies_Equation2 (G : Type*) [Magma G] (h : Equation17445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation17446_implies_Equation2 (G : Type*) [Magma G] (h : Equation17446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17448_implies_Equation2 (G : Type*) [Magma G] (h : Equation17448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17449_implies_Equation2 (G : Type*) [Magma G] (h : Equation17449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17450_implies_Equation2 (G : Type*) [Magma G] (h : Equation17450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17451_implies_Equation2 (G : Type*) [Magma G] (h : Equation17451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17453_implies_Equation2 (G : Type*) [Magma G] (h : Equation17453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq60 eq16


@[equational_result]
theorem Equation17454_implies_Equation2 (G : Type*) [Magma G] (h : Equation17454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq47 eq14


@[equational_result]
theorem Equation17455_implies_Equation2 (G : Type*) [Magma G] (h : Equation17455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation17456_implies_Equation2 (G : Type*) [Magma G] (h : Equation17456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : ((X1 ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation17458_implies_Equation2 (G : Type*) [Magma G] (h : Equation17458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17459_implies_Equation2 (G : Type*) [Magma G] (h : Equation17459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17460_implies_Equation2 (G : Type*) [Magma G] (h : Equation17460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17461_implies_Equation2 (G : Type*) [Magma G] (h : Equation17461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17463_implies_Equation2 (G : Type*) [Magma G] (h : Equation17463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17464_implies_Equation2 (G : Type*) [Magma G] (h : Equation17464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17465_implies_Equation2 (G : Type*) [Magma G] (h : Equation17465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17466_implies_Equation2 (G : Type*) [Magma G] (h : Equation17466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17468_implies_Equation2 (G : Type*) [Magma G] (h : Equation17468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17469_implies_Equation2 (G : Type*) [Magma G] (h : Equation17469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17470_implies_Equation2 (G : Type*) [Magma G] (h : Equation17470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17471_implies_Equation2 (G : Type*) [Magma G] (h : Equation17471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17473_implies_Equation2 (G : Type*) [Magma G] (h : Equation17473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17474_implies_Equation2 (G : Type*) [Magma G] (h : Equation17474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17475_implies_Equation2 (G : Type*) [Magma G] (h : Equation17475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17476_implies_Equation2 (G : Type*) [Magma G] (h : Equation17476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17477_implies_Equation2 (G : Type*) [Magma G] (h : Equation17477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17479_implies_Equation2 (G : Type*) [Magma G] (h : Equation17479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X0))) := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq9 eq9
  have eq25 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq16 eq13
  have eq31 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq25 eq15
  have eq34 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq25 eq31
  have eq35 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq25 eq34
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq35 eq35
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq41 eq36


@[equational_result]
theorem Equation17480_implies_Equation2 (G : Type*) [Magma G] (h : Equation17480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq12 eq12
  have eq15 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq12 eq12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))))) = X2 := superpose eq9 eq9
  have eq28 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq12 eq9
  have eq29 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq9 eq9
  have eq31 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq9
  have eq37 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq12 eq28
  have eq38 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq37
  have eq42 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq31 eq15
  have eq45 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq42 eq38
  have eq50 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq31 eq7
  have eq52 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq31 eq9
  have eq53 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq31 eq50
  have eq54 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq31 eq53
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq54 eq13
  have eq57 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq56 eq52
  have eq58 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq45 eq57
  have eq59 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq22 eq58
  have eq61 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0)))) = X3 := superpose eq59 eq9
  have eq72 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq59 eq61
  have eq73 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq72 eq29
  have eq80 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq72 eq73
  have eq91 (X0 X2 : G) : X0 = X2 := superpose eq80 eq80
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq91 eq8
  subsumption eq117 eq91


@[equational_result]
theorem Equation17481_implies_Equation2 (G : Type*) [Magma G] (h : Equation17481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X4 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq9 eq9
  have eq26 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq16 eq9
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq26 eq16
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq26 eq28
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq32 eq32
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq38 eq33


@[equational_result]
theorem Equation17483_implies_Equation2 (G : Type*) [Magma G] (h : Equation17483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq7 eq11
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq12 eq7
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X1)) = X0 := superpose eq12 eq18
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation17485_implies_Equation2 (G : Type*) [Magma G] (h : Equation17485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X5)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X6 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X6)))) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq9 eq9
  have eq25 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq18 eq13
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq25 eq15
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq25 eq28
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq40 eq35


@[equational_result]
theorem Equation17488_implies_Equation2 (G : Type*) [Magma G] (h : Equation17488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq12
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq26
  have eq35 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq34 eq14
  have eq37 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))))) = X3 := superpose eq35 eq9
  have eq40 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2))))) = X3 := superpose eq35 eq37
  have eq41 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2)))) = X3 := superpose eq35 eq40
  have eq42 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq35 eq41
  have eq43 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = X3 := superpose eq34 eq42
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq61 eq55


@[equational_result]
theorem Equation17489_implies_Equation2 (G : Type*) [Magma G] (h : Equation17489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X0))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X5 X6 : G) : ((X1 ◇ X0) ◇ (X5 ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq10
  have eq25 (X0 X1 X2 X4 X5 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X4 ◇ X5))))) := superpose eq7 eq11
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X0) := superpose eq13 eq25
  have eq46 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq7 eq42
  have eq105 (X0 X2 : G) : X0 = X2 := superpose eq10 eq46
  have eq209 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq209 eq105


@[equational_result]
theorem Equation17491_implies_Equation2 (G : Type*) [Magma G] (h : Equation17491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := superpose eq7 eq9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq25 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq18 eq15
  have eq32 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq25 eq17
  have eq34 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq25 eq32
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq40 eq35


@[equational_result]
theorem Equation17492_implies_Equation2 (G : Type*) [Magma G] (h : Equation17492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ (X4 ◇ (X4 ◇ X0))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) = ((X4 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) := superpose eq7 eq12
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ X1)) := superpose eq12 eq12
  have eq18 (X0 X1 X4 X5 : G) : (X0 ◇ X1) = ((X4 ◇ (X5 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq12 eq12
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = ((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3))) := superpose eq12 eq7
  have eq24 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = ((X4 ◇ X3) ◇ (X2 ◇ X3)) := superpose eq18 eq20
  have eq25 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq16 eq24
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) := superpose eq25 eq13
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X0))) = X4 := superpose eq25 eq10
  have eq31 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X2)) = X0 := superpose eq25 eq7
  have eq35 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ (X2 ◇ X3))) := superpose eq25 eq26
  have eq36 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ X3)) := superpose eq25 eq35
  have eq41 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) = X4 := superpose eq36 eq29
  have eq42 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X4 ◇ X0)) = X4 := superpose eq36 eq41
  have eq43 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq42 eq16
  have eq52 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq43 eq31
  have eq53 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq43 eq52
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq53 eq53
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq56 eq54


@[equational_result]
theorem Equation17493_implies_Equation2 (G : Type*) [Magma G] (h : Equation17493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X5 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq19 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X5))) = X4 := superpose eq14 eq9
  have eq21 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X5)) = X4 := superpose eq14 eq19
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation17494_implies_Equation2 (G : Type*) [Magma G] (h : Equation17494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ (X5 ◇ (X5 ◇ (X6 ◇ X7)))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq23 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq16 eq13
  have eq29 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq23 eq15
  have eq32 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq23 eq29
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq32 eq32
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq52 eq41


@[equational_result]
theorem Equation17496_implies_Equation2 (G : Type*) [Magma G] (h : Equation17496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq11
  have eq26 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ X4)))) ◇ X0))) = X2 := superpose eq9 eq9
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq15
  have eq49 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq15 eq36
  have eq53 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq49 eq26
  have eq59 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq53
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq7 eq59
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq100 eq60


@[equational_result]
theorem Equation17498_implies_Equation2 (G : Type*) [Magma G] (h : Equation17498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X4 := superpose eq7 eq11
  have eq36 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))) = X3 := superpose eq9 eq7
  have eq46 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq9
  have eq57 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = X3 := superpose eq46 eq36
  have eq68 (X0 X2 : G) : X0 = X2 := superpose eq11 eq57
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq82 eq68


@[equational_result]
theorem Equation17500_implies_Equation2 (G : Type*) [Magma G] (h : Equation17500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq9
  have eq74 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X2 := superpose eq10 eq9
  have eq103 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq12 eq74
  have eq109 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq103 eq12
  have eq118 (X0 X3 : G) : X0 = X3 := superpose eq109 eq109
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq126 eq118


@[equational_result]
theorem Equation17501_implies_Equation2 (G : Type*) [Magma G] (h : Equation17501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq7
  have eq22 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq9 eq11
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X0 ◇ X0) := superpose eq9 eq11
  have eq32 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq25 eq18
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ X2)) := superpose eq7 eq22
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq22 eq9
  have eq51 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq39 eq35
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq39 eq51
  have eq60 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq59 eq32
  have eq69 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq59 eq60
  have eq73 (X0 X2 : G) : X0 = X2 := superpose eq69 eq69
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq75 eq73


@[equational_result]
theorem Equation17502_implies_Equation2 (G : Type*) [Magma G] (h : Equation17502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq27 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq11
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq27 eq7
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq47 eq47
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq71 eq56


@[equational_result]
theorem Equation17504_implies_Equation2 (G : Type*) [Magma G] (h : Equation17504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq76 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq10 eq7
  have eq77 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq9
  have eq88 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq77 eq76
  have eq109 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq88
  have eq126 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq109 eq88
  have eq139 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq126 eq11
  have eq142 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X3 := superpose eq139 eq10
  have eq198 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq139 eq142
  have eq199 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq139 eq198
  have eq200 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq139 eq199
  have eq201 (X0 X3 : G) : X0 = X3 := superpose eq200 eq200
  have eq206 (X0 : G) : sK0 ≠ X0 := superpose eq201 eq8
  subsumption eq206 eq201


@[equational_result]
theorem Equation17506_implies_Equation2 (G : Type*) [Magma G] (h : Equation17506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq12 eq12
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) = X3 := superpose eq12 eq7
  have eq36 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = X3 := superpose eq12 eq11
  have eq52 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq36 eq17
  have eq57 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1)))) = X3 := superpose eq52 eq21
  have eq74 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X3 := superpose eq52 eq57
  have eq75 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq52 eq74
  have eq80 (X0 X1 : G) : X0 = X1 := superpose eq52 eq75
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq82 eq80


@[equational_result]
theorem Equation17508_implies_Equation2 (G : Type*) [Magma G] (h : Equation17508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X5 ◇ (X1 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq15 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq25 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq15 eq9
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq25 eq25
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq25 eq31
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq63 eq32


@[equational_result]
theorem Equation17509_implies_Equation2 (G : Type*) [Magma G] (h : Equation17509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq35 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) ◇ (X5 ◇ (X0 ◇ X4)))) ◇ (X6 ◇ X7)) = X6 := superpose eq11 eq11
  have eq61 (X0 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X7)) = X6 := superpose eq11 eq35
  have eq66 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X4 := superpose eq61 eq11
  have eq84 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq66 eq66
  have eq95 (X0 X3 : G) : X0 = X3 := superpose eq66 eq84
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq132 eq95


@[equational_result]
theorem Equation17510_implies_Equation2 (G : Type*) [Magma G] (h : Equation17510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq26 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = X0 := superpose eq7 eq12
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq126 eq58


@[equational_result]
theorem Equation17511_implies_Equation2 (G : Type*) [Magma G] (h : Equation17511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X5 ◇ X6) ◇ X5) = X0 := superpose eq7 eq12
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq118 eq55


@[equational_result]
theorem Equation17514_implies_Equation2 (G : Type*) [Magma G] (h : Equation17514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ ((X3 ◇ X2) ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0))) := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))))) ◇ X0))) = X1 := superpose eq9 eq9
  have eq37 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ ((X3 ◇ (X1 ◇ (X3 ◇ X1))) ◇ X3))) ◇ (X3 ◇ (((X0 ◇ X1) ◇ ((X3 ◇ (X1 ◇ (X3 ◇ X1))) ◇ X3)) ◇ (X0 ◇ X1)))) = X3 := superpose eq13 eq7
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0)) ◇ (X1 ◇ X2)))) = X0 := superpose eq7 eq14
  have eq67 (X0 : G) : (((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) ◇ X0) ◇ (((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) = X0 := superpose eq13 eq46
  have eq341 (X0 X1 : G) : ((X1 ◇ (((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) ◇ (((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) = X0 := superpose eq13 eq37
  have eq1333 (X0 : G) : (X0 ◇ (X0 ◇ ((((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) ◇ X0)))) = X0 := superpose eq67 eq37
  have eq1347 (X0 : G) : (X0 ◇ (((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) = X0 := superpose eq13 eq1333
  have eq1372 (X0 : G) : ((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) ◇ X0) = X0 := superpose eq13 eq1347
  have eq1383 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) = X0 := superpose eq1372 eq67
  have eq1385 (X0 X1 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) = X0 := superpose eq1372 eq341
  have eq1482 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = ((X2 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0)) := superpose eq1372 eq10
  have eq1493 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq1372 eq7
  have eq1594 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) = X1 := superpose eq1493 eq1493
  have eq1605 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) = X1 := superpose eq1493 eq9
  have eq1694 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0)) := superpose eq1372 eq1605
  have eq1729 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ X0) := superpose eq1594 eq7
  have eq1748 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq1729 eq1694
  have eq1749 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq1493 eq1748
  have eq1751 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq1749 eq1383
  have eq1752 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq1749 eq1385
  have eq1758 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq1749 eq1482
  have eq1775 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq1751 eq1729
  have eq1785 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose eq1775 eq1758
  have eq1786 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq1751 eq1785
  have eq1787 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq1752 eq1786
  have eq1788 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq1787 eq7
  have eq2013 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq1787 eq1788
  have eq2014 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq1787 eq2013
  have eq2015 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq1787 eq2014
  have eq2021 (X0 X2 : G) : X0 = X2 := superpose eq2015 eq2015
  have eq2023 (X0 : G) : sK0 ≠ X0 := superpose eq2021 eq8
  subsumption eq2023 eq2021


@[equational_result]
theorem Equation17515_implies_Equation2 (G : Type*) [Magma G] (h : Equation17515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X4 := superpose eq7 eq11
  have eq24 (X0 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ (X0 ◇ (X5 ◇ X6))) = X0 := superpose eq7 eq10
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq14 eq14
  have eq110 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq39 eq14
  have eq138 (X0 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ X6) = X0 := superpose eq110 eq24
  have eq188 (X0 X4 : G) : X0 = X4 := superpose eq138 eq138
  have eq211 (X0 : G) : sK0 ≠ X0 := superpose eq188 eq8
  subsumption eq211 eq188


@[equational_result]
theorem Equation17518_implies_Equation2 (G : Type*) [Magma G] (h : Equation17518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0) ◇ X0) = X0 := superpose eq7 eq10
  have eq19 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq9 eq9
  have eq25 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq7 eq19
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq19 eq7
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = X2 := superpose eq19 eq7
  have eq51 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq29 eq11
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq25 eq51
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq62 eq7
  have eq95 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq19 eq64
  have eq98 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq19 eq64
  have eq101 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq95 eq62
  have eq103 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq101 eq33
  have eq127 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq101 eq98
  have eq129 (X0 X1 : G) : X0 = X1 := superpose eq103 eq127
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq134 eq129


@[equational_result]
theorem Equation17519_implies_Equation2 (G : Type*) [Magma G] (h : Equation17519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq12 eq11
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq11 eq42
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq112 eq61


@[equational_result]
theorem Equation17523_implies_Equation2 (G : Type*) [Magma G] (h : Equation17523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq12 eq12
  have eq28 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq11
  have eq48 (X0 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := superpose eq7 eq19
  have eq86 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq48 eq28
  have eq131 (X0 X3 : G) : X0 = X3 := superpose eq11 eq86
  have eq205 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq205 eq131


@[equational_result]
theorem Equation17525_implies_Equation2 (G : Type*) [Magma G] (h : Equation17525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X1 := superpose eq12 eq7
  have eq44 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ (X4 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (X5 ◇ X6)) = X5 := superpose eq12 eq11
  have eq62 (X1 X5 X6 : G) : (X1 ◇ (X5 ◇ X6)) = X5 := superpose eq27 eq44
  have eq101 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq62 eq62
  have eq106 (X0 X3 : G) : X0 = X3 := superpose eq101 eq101
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq143 eq106


@[equational_result]
theorem Equation17526_implies_Equation2 (G : Type*) [Magma G] (h : Equation17526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X5 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X3))) ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3))))))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X3))) ◇ (X5 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))))))) = X6 := superpose eq11 eq9
  have eq52 (X0 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := superpose eq7 eq21
  have eq98 (X1 X2 X6 : G) : (X2 ◇ X1) = X6 := superpose eq52 eq45
  have eq107 (X0 X4 : G) : X0 = X4 := superpose eq7 eq98
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq136 eq107


@[equational_result]
theorem Equation17527_implies_Equation2 (G : Type*) [Magma G] (h : Equation17527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X5 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X1)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq39 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ (X5 ◇ (X0 ◇ (X1 ◇ X1)))) = X5 := superpose eq7 eq10
  have eq53 (X0 X1 X3 X4 : G) : (X1 ◇ X0) = ((X3 ◇ X4) ◇ X4) := superpose eq10 eq11
  have eq90 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X5)))) ◇ (X6 ◇ (X0 ◇ X1))) = X6 := superpose eq53 eq10
  have eq92 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X3 ◇ (X4 ◇ X4))) ◇ (X5 ◇ (X0 ◇ X1))) = X5 := superpose eq53 eq7
  have eq119 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X6 ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X4 ◇ X4))) ◇ (X5 ◇ X5)))) = X6 := superpose eq9 eq9
  have eq144 (X0 X3 X5 X6 : G) : (X0 ◇ (X6 ◇ (X3 ◇ (X5 ◇ X5)))) = X6 := superpose eq92 eq119
  have eq145 (X0 X1 X3 X6 : G) : (X3 ◇ (X6 ◇ (X0 ◇ X1))) = X6 := superpose eq144 eq90
  have eq156 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X0) = X5 := superpose eq145 eq39
  have eq173 (X0 X3 X5 : G) : (X3 ◇ X0) = X5 := superpose eq145 eq156
  have eq177 (X0 X3 : G) : X0 = X3 := superpose eq173 eq173
  have eq229 (X0 : G) : sK0 ≠ X0 := superpose eq177 eq8
  subsumption eq229 eq177


@[equational_result]
theorem Equation17528_implies_Equation2 (G : Type*) [Magma G] (h : Equation17528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ (X5 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X6 ◇ X7)))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq11 eq9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq13 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation17530_implies_Equation2 (G : Type*) [Magma G] (h : Equation17530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X4 ◇ (X1 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq32 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq9
  have eq38 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq9 eq9
  have eq57 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq38 eq32
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq57 eq57
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq103 eq65


@[equational_result]
theorem Equation17531_implies_Equation2 (G : Type*) [Magma G] (h : Equation17531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X4 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X2))))))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = (X0 ◇ X0) := superpose eq7 eq12
  have eq35 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X4 ◇ (X0 ◇ X0))))) = X4 := superpose eq19 eq9
  have eq38 (X0 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X4 := superpose eq19 eq35
  have eq47 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq12 eq38
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq47 eq47
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq101 eq57


@[equational_result]
theorem Equation17532_implies_Equation2 (G : Type*) [Magma G] (h : Equation17532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ ((X0 ◇ (X5 ◇ (X0 ◇ X5))) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq11 eq11
  have eq19 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X0 ◇ X0))) := superpose eq15 eq10
  have eq20 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq11 eq19
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq20
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq29
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq108 eq49


@[equational_result]
theorem Equation17533_implies_Equation2 (G : Type*) [Magma G] (h : Equation17533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq29
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation17535_implies_Equation2 (G : Type*) [Magma G] (h : Equation17535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X1) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq147 eq58


@[equational_result]
theorem Equation17536_implies_Equation2 (G : Type*) [Magma G] (h : Equation17536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq95 eq34


@[equational_result]
theorem Equation17537_implies_Equation2 (G : Type*) [Magma G] (h : Equation17537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ ((X0 ◇ (X5 ◇ (X1 ◇ X5))) ◇ X0))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq11 eq12
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X0 ◇ (X5 ◇ (X1 ◇ X5))))) = X4 := superpose eq13 eq10
  have eq18 (X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ X4) = X4 := superpose eq13 eq14
  have eq19 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X4) = X4 := superpose eq13 eq18
  have eq20 (X1 X4 : G) : (X1 ◇ X4) = X4 := superpose eq13 eq19
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq13 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation17538_implies_Equation2 (G : Type*) [Magma G] (h : Equation17538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X5 : G) : (X0 ◇ (X5 ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq13 eq7
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq11 eq21
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq35 eq26


@[equational_result]
theorem Equation17540_implies_Equation2 (G : Type*) [Magma G] (h : Equation17540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((X1 ◇ X2) ◇ X3) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq115 eq45


@[equational_result]
theorem Equation17541_implies_Equation2 (G : Type*) [Magma G] (h : Equation17541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ ((X0 ◇ (X3 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X2))))))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X2 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq10 eq9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq12 eq12
  have eq26 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X3) := superpose eq12 eq11
  have eq49 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq16 eq26
  have eq60 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq49 eq12
  have eq61 (X0 X2 : G) : X0 = X2 := superpose eq60 eq60
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq72 eq61


@[equational_result]
theorem Equation17542_implies_Equation2 (G : Type*) [Magma G] (h : Equation17542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ ((X0 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X5)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X4))))) = X0 := superpose eq9 eq9
  have eq56 (X0 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := superpose eq7 eq21
  have eq100 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq56 eq47
  have eq233 (X0 X2 : G) : X0 = X2 := superpose eq100 eq100
  have eq238 (X0 : G) : sK0 ≠ X0 := superpose eq233 eq8
  subsumption eq238 eq233


@[equational_result]
theorem Equation17543_implies_Equation2 (G : Type*) [Magma G] (h : Equation17543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq29
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq119 eq49


@[equational_result]
theorem Equation17545_implies_Equation2 (G : Type*) [Magma G] (h : Equation17545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X5 ◇ (X1 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq32 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq9
  have eq38 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq9 eq9
  have eq58 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq38 eq32
  have eq66 (X0 X3 : G) : X0 = X3 := superpose eq58 eq58
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq110 eq66


@[equational_result]
theorem Equation17546_implies_Equation2 (G : Type*) [Magma G] (h : Equation17546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ (X3 ◇ X1))) ◇ (X4 ◇ (X0 ◇ X1))) = X4 := superpose eq7 eq7
  have eq39 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq11
  have eq40 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X3))) = X4 := superpose eq11 eq11
  have eq74 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq40 eq39
  have eq82 (X0 X3 : G) : X0 = X3 := superpose eq74 eq74
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq115 eq82


@[equational_result]
theorem Equation17547_implies_Equation2 (G : Type*) [Magma G] (h : Equation17547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X5 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X4 ◇ (X4 ◇ X4))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq10
  have eq32 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1)))) = X4 := superpose eq9 eq10
  have eq40 (X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X1) = X4 := superpose eq28 eq32
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq40
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq112 eq46


@[equational_result]
theorem Equation17548_implies_Equation2 (G : Type*) [Magma G] (h : Equation17548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation17550_implies_Equation2 (G : Type*) [Magma G] (h : Equation17550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = (((X1 ◇ X2) ◇ X3) ◇ X0) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq61 (X0 X5 : G) : X0 = X5 := superpose eq7 eq22
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq140 eq61


@[equational_result]
theorem Equation17551_implies_Equation2 (G : Type*) [Magma G] (h : Equation17551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq61 (X0 X5 : G) : X0 = X5 := superpose eq7 eq22
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq154 eq61


@[equational_result]
theorem Equation17552_implies_Equation2 (G : Type*) [Magma G] (h : Equation17552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X5) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq12
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq11 eq34
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq78 eq43


@[equational_result]
theorem Equation17553_implies_Equation2 (G : Type*) [Magma G] (h : Equation17553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation17554_implies_Equation2 (G : Type*) [Magma G] (h : Equation17554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X6 X7 X8 X9 : G) : (X0 ◇ (X6 ◇ (X7 ◇ (X8 ◇ X9)))) = X6 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq11
  have eq21 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq13 eq9
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq11 eq21
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq33 eq24


@[equational_result]
theorem Equation17556_implies_Equation2 (G : Type*) [Magma G] (h : Equation17556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq11
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq13 eq7
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq13 eq18
  have eq23 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq13 eq22
  have eq24 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq13 eq23
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation17558_implies_Equation2 (G : Type*) [Magma G] (h : Equation17558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X4 ◇ (X4 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 : G) : (X1 ◇ X2) = ((X0 ◇ X4) ◇ (X1 ◇ X2)) := superpose eq7 eq11
  have eq19 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X4 ◇ X5))) = X4 := superpose eq12 eq9
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq19 eq7
  have eq21 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq20 eq11
  have eq24 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq21 eq19
  have eq26 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq21 eq24
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq32 eq27


@[equational_result]
theorem Equation17560_implies_Equation2 (G : Type*) [Magma G] (h : Equation17560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq11
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X1)) = X0 := superpose eq12 eq7
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq36 eq27


@[equational_result]
theorem Equation17561_implies_Equation2 (G : Type*) [Magma G] (h : Equation17561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq9
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := superpose eq24 eq10
  have eq44 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq24 eq33
  have eq45 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq24 eq44
  have eq46 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq24 eq45
  have eq56 (X0 X1 : G) : X0 = X1 := superpose eq46 eq24
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq58 eq56


@[equational_result]
theorem Equation17562_implies_Equation2 (G : Type*) [Magma G] (h : Equation17562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq122 eq48


@[equational_result]
theorem Equation17565_implies_Equation2 (G : Type*) [Magma G] (h : Equation17565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X2) = ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq11 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq11 eq10
  have eq36 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) := superpose eq10 eq11
  have eq58 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq14
  have eq78 (X0 X1 X2 : G) : (X2 ◇ X1) = ((((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) := superpose eq14 eq11
  have eq134 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq58 eq58
  have eq162 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) := superpose eq134 eq36
  have eq181 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq78 eq162
  have eq215 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))))) = X3 := superpose eq181 eq9
  have eq239 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq181 eq20
  have eq306 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X3 := superpose eq181 eq215
  have eq329 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = X3 := superpose eq239 eq306
  have eq397 (X0 X3 : G) : X0 = X3 := superpose eq329 eq329
  have eq399 (X0 : G) : sK0 ≠ X0 := superpose eq397 eq8
  subsumption eq399 eq397


@[equational_result]
theorem Equation17566_implies_Equation2 (G : Type*) [Magma G] (h : Equation17566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq128 eq53


@[equational_result]
theorem Equation17568_implies_Equation2 (G : Type*) [Magma G] (h : Equation17568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq43 eq17


@[equational_result]
theorem Equation17569_implies_Equation2 (G : Type*) [Magma G] (h : Equation17569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq63 eq18


@[equational_result]
theorem Equation17570_implies_Equation2 (G : Type*) [Magma G] (h : Equation17570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X1 := superpose eq7 eq10
  have eq34 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq12 eq10
  have eq40 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq17 eq34
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq7 eq40
  have eq111 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq111 eq41


@[equational_result]
theorem Equation17571_implies_Equation2 (G : Type*) [Magma G] (h : Equation17571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq40 eq17


@[equational_result]
theorem Equation17573_implies_Equation2 (G : Type*) [Magma G] (h : Equation17573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq74 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X3) = (((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) ◇ X5) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) ◇ X4))) := superpose eq10 eq10
  have eq87 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) ◇ X4) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1))) ◇ X3)) = X0 := superpose eq10 eq11
  have eq112 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq87 eq74
  have eq119 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq112 eq7
  have eq169 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq112 eq119
  have eq171 (X0 X2 : G) : X0 = X2 := superpose eq169 eq169
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq171 eq8
  subsumption eq173 eq171


@[equational_result]
theorem Equation17575_implies_Equation2 (G : Type*) [Magma G] (h : Equation17575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq46 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq57 eq46


@[equational_result]
theorem Equation17577_implies_Equation2 (G : Type*) [Magma G] (h : Equation17577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17578_implies_Equation2 (G : Type*) [Magma G] (h : Equation17578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation17579_implies_Equation2 (G : Type*) [Magma G] (h : Equation17579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17581_implies_Equation2 (G : Type*) [Magma G] (h : Equation17581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17582_implies_Equation2 (G : Type*) [Magma G] (h : Equation17582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17583_implies_Equation2 (G : Type*) [Magma G] (h : Equation17583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17585_implies_Equation2 (G : Type*) [Magma G] (h : Equation17585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17586_implies_Equation2 (G : Type*) [Magma G] (h : Equation17586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17587_implies_Equation2 (G : Type*) [Magma G] (h : Equation17587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17588_implies_Equation2 (G : Type*) [Magma G] (h : Equation17588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17592_implies_Equation2 (G : Type*) [Magma G] (h : Equation17592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq40 eq16


@[equational_result]
theorem Equation17594_implies_Equation2 (G : Type*) [Magma G] (h : Equation17594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17595_implies_Equation2 (G : Type*) [Magma G] (h : Equation17595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation17596_implies_Equation2 (G : Type*) [Magma G] (h : Equation17596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17598_implies_Equation2 (G : Type*) [Magma G] (h : Equation17598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17599_implies_Equation2 (G : Type*) [Magma G] (h : Equation17599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17600_implies_Equation2 (G : Type*) [Magma G] (h : Equation17600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17602_implies_Equation2 (G : Type*) [Magma G] (h : Equation17602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17603_implies_Equation2 (G : Type*) [Magma G] (h : Equation17603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17604_implies_Equation2 (G : Type*) [Magma G] (h : Equation17604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17605_implies_Equation2 (G : Type*) [Magma G] (h : Equation17605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17607_implies_Equation2 (G : Type*) [Magma G] (h : Equation17607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation17608_implies_Equation2 (G : Type*) [Magma G] (h : Equation17608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq71 eq20


@[equational_result]
theorem Equation17609_implies_Equation2 (G : Type*) [Magma G] (h : Equation17609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq50 eq19


@[equational_result]
theorem Equation17610_implies_Equation2 (G : Type*) [Magma G] (h : Equation17610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation17612_implies_Equation2 (G : Type*) [Magma G] (h : Equation17612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17613_implies_Equation2 (G : Type*) [Magma G] (h : Equation17613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17614_implies_Equation2 (G : Type*) [Magma G] (h : Equation17614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17615_implies_Equation2 (G : Type*) [Magma G] (h : Equation17615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17617_implies_Equation2 (G : Type*) [Magma G] (h : Equation17617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17618_implies_Equation2 (G : Type*) [Magma G] (h : Equation17618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17619_implies_Equation2 (G : Type*) [Magma G] (h : Equation17619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17620_implies_Equation2 (G : Type*) [Magma G] (h : Equation17620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17622_implies_Equation2 (G : Type*) [Magma G] (h : Equation17622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17623_implies_Equation2 (G : Type*) [Magma G] (h : Equation17623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17624_implies_Equation2 (G : Type*) [Magma G] (h : Equation17624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17625_implies_Equation2 (G : Type*) [Magma G] (h : Equation17625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17627_implies_Equation2 (G : Type*) [Magma G] (h : Equation17627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17628_implies_Equation2 (G : Type*) [Magma G] (h : Equation17628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17629_implies_Equation2 (G : Type*) [Magma G] (h : Equation17629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17630_implies_Equation2 (G : Type*) [Magma G] (h : Equation17630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17631_implies_Equation2 (G : Type*) [Magma G] (h : Equation17631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17634_implies_Equation2 (G : Type*) [Magma G] (h : Equation17634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X3 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq11
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq11 eq7
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq13
  have eq28 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq12 eq7
  have eq33 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq28
  have eq34 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := superpose eq33 eq15
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq12 eq10
  have eq44 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))))) = ((X4 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))))) ◇ (X3 ◇ X0))) ◇ ((((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))))) ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))))) ◇ X3))) := superpose eq9 eq10
  have eq57 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq33 eq42
  have eq58 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq34 eq57
  have eq59 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq12 eq58
  have eq60 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq34 eq59
  have eq61 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))))) = ((X4 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))))) ◇ (X3 ◇ X0))) ◇ ((((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))))) ◇ (X3 ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3)))) := superpose eq60 eq44
  have eq62 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))))) = ((X4 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))))) ◇ (X3 ◇ X0))) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq34 eq61
  have eq63 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))))) = ((X3 ◇ X3) ◇ (X3 ◇ X3)) := superpose eq34 eq62
  have eq64 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))))) = (X3 ◇ X3) := superpose eq33 eq63
  have eq88 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq34 eq7
  have eq104 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq88
  have eq105 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq104 eq60
  have eq109 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))))) = X3 := superpose eq105 eq64
  have eq131 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))))) = X3 := superpose eq105 eq109
  have eq132 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2))))) = X3 := superpose eq105 eq131
  have eq133 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) = X3 := superpose eq105 eq132
  have eq134 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X3 ◇ X2))) = X3 := superpose eq105 eq133
  have eq135 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = X3 := superpose eq105 eq134
  have eq136 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq105 eq135
  have eq137 (X0 X3 : G) : X0 = X3 := superpose eq136 eq136
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq137 eq8
  subsumption eq139 eq137


@[equational_result]
theorem Equation17635_implies_Equation2 (G : Type*) [Magma G] (h : Equation17635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X4 ◇ (X4 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq7 eq10
  have eq37 (X0 X3 X4 : G) : (X0 ◇ (X0 ◇ X3)) = X4 := superpose eq28 eq9
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq68 eq43


@[equational_result]
theorem Equation17638_implies_Equation2 (G : Type*) [Magma G] (h : Equation17638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq14
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq32 eq23


@[equational_result]
theorem Equation17639_implies_Equation2 (G : Type*) [Magma G] (h : Equation17639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X1 ◇ X2) ◇ (X2 ◇ X0)) := superpose eq7 eq7
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq128 eq53


@[equational_result]
theorem Equation17642_implies_Equation2 (G : Type*) [Magma G] (h : Equation17642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq7
  have eq20 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq7
  have eq24 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X0 := superpose eq20 eq12
  have eq27 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) = X3 := superpose eq24 eq9
  have eq30 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq24 eq27
  have eq31 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq20 eq30
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq11 eq31
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq39 eq32


@[equational_result]
theorem Equation17643_implies_Equation2 (G : Type*) [Magma G] (h : Equation17643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X2) ◇ (X2 ◇ X0)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq122 eq49


@[equational_result]
theorem Equation17645_implies_Equation2 (G : Type*) [Magma G] (h : Equation17645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq56 eq19


@[equational_result]
theorem Equation17646_implies_Equation2 (G : Type*) [Magma G] (h : Equation17646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X2))) ◇ (X4 ◇ (X5 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2))))))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X2)) = X4 := superpose eq12 eq9
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq50 eq19


@[equational_result]
theorem Equation17647_implies_Equation2 (G : Type*) [Magma G] (h : Equation17647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X3))) ◇ (X4 ◇ (X5 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq10
  have eq23 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X3)) = X4 := superpose eq17 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq52 eq30


@[equational_result]
theorem Equation17648_implies_Equation2 (G : Type*) [Magma G] (h : Equation17648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ (X5 ◇ (X6 ◇ X7)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ X4)) = X5 := superpose eq12 eq9
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation17652_implies_Equation2 (G : Type*) [Magma G] (h : Equation17652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq42 eq17


@[equational_result]
theorem Equation17654_implies_Equation2 (G : Type*) [Magma G] (h : Equation17654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17655_implies_Equation2 (G : Type*) [Magma G] (h : Equation17655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17656_implies_Equation2 (G : Type*) [Magma G] (h : Equation17656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17658_implies_Equation2 (G : Type*) [Magma G] (h : Equation17658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17659_implies_Equation2 (G : Type*) [Magma G] (h : Equation17659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17660_implies_Equation2 (G : Type*) [Magma G] (h : Equation17660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17662_implies_Equation2 (G : Type*) [Magma G] (h : Equation17662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17663_implies_Equation2 (G : Type*) [Magma G] (h : Equation17663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17664_implies_Equation2 (G : Type*) [Magma G] (h : Equation17664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17665_implies_Equation2 (G : Type*) [Magma G] (h : Equation17665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17668_implies_Equation2 (G : Type*) [Magma G] (h : Equation17668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))))) ◇ (((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))))) ◇ (((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))))) ◇ X0))) = X3 := superpose eq9 eq7
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))))) ◇ (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))))) ◇ (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))))) ◇ X3)))))) = X4 := superpose eq10 eq9
  have eq39 (X1 X2 X4 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2))) = X4 := superpose eq15 eq33
  have eq138 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq138 eq8
  subsumption eq153 eq138


@[equational_result]
theorem Equation17669_implies_Equation2 (G : Type*) [Magma G] (h : Equation17669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq57 eq46


@[equational_result]
theorem Equation17671_implies_Equation2 (G : Type*) [Magma G] (h : Equation17671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17672_implies_Equation2 (G : Type*) [Magma G] (h : Equation17672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation17673_implies_Equation2 (G : Type*) [Magma G] (h : Equation17673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17675_implies_Equation2 (G : Type*) [Magma G] (h : Equation17675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17676_implies_Equation2 (G : Type*) [Magma G] (h : Equation17676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17677_implies_Equation2 (G : Type*) [Magma G] (h : Equation17677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17679_implies_Equation2 (G : Type*) [Magma G] (h : Equation17679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17680_implies_Equation2 (G : Type*) [Magma G] (h : Equation17680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17681_implies_Equation2 (G : Type*) [Magma G] (h : Equation17681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17682_implies_Equation2 (G : Type*) [Magma G] (h : Equation17682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17684_implies_Equation2 (G : Type*) [Magma G] (h : Equation17684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq74 eq22


@[equational_result]
theorem Equation17685_implies_Equation2 (G : Type*) [Magma G] (h : Equation17685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation17686_implies_Equation2 (G : Type*) [Magma G] (h : Equation17686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq45 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq12 eq12
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq45
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq118 eq56


@[equational_result]
theorem Equation17687_implies_Equation2 (G : Type*) [Magma G] (h : Equation17687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation17689_implies_Equation2 (G : Type*) [Magma G] (h : Equation17689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17690_implies_Equation2 (G : Type*) [Magma G] (h : Equation17690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17691_implies_Equation2 (G : Type*) [Magma G] (h : Equation17691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17692_implies_Equation2 (G : Type*) [Magma G] (h : Equation17692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17694_implies_Equation2 (G : Type*) [Magma G] (h : Equation17694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17695_implies_Equation2 (G : Type*) [Magma G] (h : Equation17695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17696_implies_Equation2 (G : Type*) [Magma G] (h : Equation17696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17697_implies_Equation2 (G : Type*) [Magma G] (h : Equation17697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17699_implies_Equation2 (G : Type*) [Magma G] (h : Equation17699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17700_implies_Equation2 (G : Type*) [Magma G] (h : Equation17700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17701_implies_Equation2 (G : Type*) [Magma G] (h : Equation17701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17702_implies_Equation2 (G : Type*) [Magma G] (h : Equation17702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17704_implies_Equation2 (G : Type*) [Magma G] (h : Equation17704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17705_implies_Equation2 (G : Type*) [Magma G] (h : Equation17705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17706_implies_Equation2 (G : Type*) [Magma G] (h : Equation17706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17707_implies_Equation2 (G : Type*) [Magma G] (h : Equation17707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17708_implies_Equation2 (G : Type*) [Magma G] (h : Equation17708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17710_implies_Equation2 (G : Type*) [Magma G] (h : Equation17710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq12
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq15 eq7
  have eq26 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq20
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq26
  have eq28 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq15 eq27
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation17711_implies_Equation2 (G : Type*) [Magma G] (h : Equation17711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X5 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X2))))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq7 eq12
  have eq22 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))))) = X5 := superpose eq15 eq9
  have eq36 (X0 X2 X3 X5 : G) : (X0 ◇ (X5 ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = X5 := superpose eq15 eq22
  have eq37 (X0 X2 X3 X5 : G) : (X0 ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2)))) = X5 := superpose eq15 eq36
  have eq38 (X0 X2 X3 X5 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X2))) = X5 := superpose eq15 eq37
  have eq39 (X0 X2 X5 : G) : (X0 ◇ (X0 ◇ X2)) = X5 := superpose eq15 eq38
  have eq40 (X0 X2 X5 : G) : (X0 ◇ X2) = X5 := superpose eq15 eq39
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq40 eq40
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq46 eq41


@[equational_result]
theorem Equation17712_implies_Equation2 (G : Type*) [Magma G] (h : Equation17712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq7 eq12
  have eq23 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := superpose eq15 eq7
  have eq27 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq15 eq23
  have eq28 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq15 eq27
  have eq29 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq15 eq28
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation17713_implies_Equation2 (G : Type*) [Magma G] (h : Equation17713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X6 ◇ X7)))) = X6 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : (X0 ◇ X5) = X5 := superpose eq7 eq12
  have eq22 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ (X6 ◇ X7))) = X6 := superpose eq14 eq9
  have eq26 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X6 := superpose eq14 eq22
  have eq27 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq14 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation17715_implies_Equation2 (G : Type*) [Magma G] (h : Equation17715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation17716_implies_Equation2 (G : Type*) [Magma G] (h : Equation17716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq41 eq27


@[equational_result]
theorem Equation17717_implies_Equation2 (G : Type*) [Magma G] (h : Equation17717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation17718_implies_Equation2 (G : Type*) [Magma G] (h : Equation17718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq61 eq16


@[equational_result]
theorem Equation17720_implies_Equation2 (G : Type*) [Magma G] (h : Equation17720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation17721_implies_Equation2 (G : Type*) [Magma G] (h : Equation17721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq62 eq16


@[equational_result]
theorem Equation17722_implies_Equation2 (G : Type*) [Magma G] (h : Equation17722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq66 eq16


@[equational_result]
theorem Equation17723_implies_Equation2 (G : Type*) [Magma G] (h : Equation17723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq61 eq16


@[equational_result]
theorem Equation17725_implies_Equation2 (G : Type*) [Magma G] (h : Equation17725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq46 eq19


@[equational_result]
theorem Equation17726_implies_Equation2 (G : Type*) [Magma G] (h : Equation17726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X2))))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ (X3 ◇ X2)))) = X3 := superpose eq7 eq12
  have eq22 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq15 eq9
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq45 eq23


@[equational_result]
theorem Equation17727_implies_Equation2 (G : Type*) [Magma G] (h : Equation17727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X4 ◇ X4)))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X4 := superpose eq7 eq11
  have eq21 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X4)) = X5 := superpose eq12 eq9
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq21
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation17728_implies_Equation2 (G : Type*) [Magma G] (h : Equation17728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation17730_implies_Equation2 (G : Type*) [Magma G] (h : Equation17730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X5 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation17731_implies_Equation2 (G : Type*) [Magma G] (h : Equation17731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X5 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq76 eq19


@[equational_result]
theorem Equation17732_implies_Equation2 (G : Type*) [Magma G] (h : Equation17732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation17733_implies_Equation2 (G : Type*) [Magma G] (h : Equation17733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X5 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation17734_implies_Equation2 (G : Type*) [Magma G] (h : Equation17734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation17736_implies_Equation2 (G : Type*) [Magma G] (h : Equation17736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X3 ◇ X0)) = X4 := superpose eq7 eq7
  have eq34 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq51 eq34


@[equational_result]
theorem Equation17737_implies_Equation2 (G : Type*) [Magma G] (h : Equation17737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq71 eq19


@[equational_result]
theorem Equation17738_implies_Equation2 (G : Type*) [Magma G] (h : Equation17738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ (X0 ◇ X4)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq12 eq11
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq12 eq15
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq43 eq17


@[equational_result]
theorem Equation17739_implies_Equation2 (G : Type*) [Magma G] (h : Equation17739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation17741_implies_Equation2 (G : Type*) [Magma G] (h : Equation17741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17742_implies_Equation2 (G : Type*) [Magma G] (h : Equation17742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17743_implies_Equation2 (G : Type*) [Magma G] (h : Equation17743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17744_implies_Equation2 (G : Type*) [Magma G] (h : Equation17744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17746_implies_Equation2 (G : Type*) [Magma G] (h : Equation17746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17747_implies_Equation2 (G : Type*) [Magma G] (h : Equation17747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17748_implies_Equation2 (G : Type*) [Magma G] (h : Equation17748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17749_implies_Equation2 (G : Type*) [Magma G] (h : Equation17749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17751_implies_Equation2 (G : Type*) [Magma G] (h : Equation17751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17752_implies_Equation2 (G : Type*) [Magma G] (h : Equation17752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17753_implies_Equation2 (G : Type*) [Magma G] (h : Equation17753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17754_implies_Equation2 (G : Type*) [Magma G] (h : Equation17754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17756_implies_Equation2 (G : Type*) [Magma G] (h : Equation17756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17757_implies_Equation2 (G : Type*) [Magma G] (h : Equation17757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17758_implies_Equation2 (G : Type*) [Magma G] (h : Equation17758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17759_implies_Equation2 (G : Type*) [Magma G] (h : Equation17759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17760_implies_Equation2 (G : Type*) [Magma G] (h : Equation17760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17762_implies_Equation2 (G : Type*) [Magma G] (h : Equation17762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq71 eq19


@[equational_result]
theorem Equation17763_implies_Equation2 (G : Type*) [Magma G] (h : Equation17763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X3 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X5 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2))))))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq11 eq11
  have eq19 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ X3)) = X5 := superpose eq13 eq9
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq44 eq24


@[equational_result]
theorem Equation17764_implies_Equation2 (G : Type*) [Magma G] (h : Equation17764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation17765_implies_Equation2 (G : Type*) [Magma G] (h : Equation17765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation17767_implies_Equation2 (G : Type*) [Magma G] (h : Equation17767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17768_implies_Equation2 (G : Type*) [Magma G] (h : Equation17768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17769_implies_Equation2 (G : Type*) [Magma G] (h : Equation17769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17770_implies_Equation2 (G : Type*) [Magma G] (h : Equation17770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17772_implies_Equation2 (G : Type*) [Magma G] (h : Equation17772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17773_implies_Equation2 (G : Type*) [Magma G] (h : Equation17773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17774_implies_Equation2 (G : Type*) [Magma G] (h : Equation17774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17775_implies_Equation2 (G : Type*) [Magma G] (h : Equation17775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17777_implies_Equation2 (G : Type*) [Magma G] (h : Equation17777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17778_implies_Equation2 (G : Type*) [Magma G] (h : Equation17778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17779_implies_Equation2 (G : Type*) [Magma G] (h : Equation17779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation17780_implies_Equation2 (G : Type*) [Magma G] (h : Equation17780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17782_implies_Equation2 (G : Type*) [Magma G] (h : Equation17782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17783_implies_Equation2 (G : Type*) [Magma G] (h : Equation17783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17784_implies_Equation2 (G : Type*) [Magma G] (h : Equation17784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17785_implies_Equation2 (G : Type*) [Magma G] (h : Equation17785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17786_implies_Equation2 (G : Type*) [Magma G] (h : Equation17786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17788_implies_Equation2 (G : Type*) [Magma G] (h : Equation17788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq45
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq143 eq57


@[equational_result]
theorem Equation17789_implies_Equation2 (G : Type*) [Magma G] (h : Equation17789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X5 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X2))))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq7 eq12
  have eq35 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X3))))) = X5 := superpose eq19 eq9
  have eq39 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X4)) = X5 := superpose eq19 eq35
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq39 eq39
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq39 eq49
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq73 eq50


@[equational_result]
theorem Equation17790_implies_Equation2 (G : Type*) [Magma G] (h : Equation17790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq11
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq28
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq109 eq45


@[equational_result]
theorem Equation17791_implies_Equation2 (G : Type*) [Magma G] (h : Equation17791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq141 eq53


@[equational_result]
theorem Equation17793_implies_Equation2 (G : Type*) [Magma G] (h : Equation17793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17794_implies_Equation2 (G : Type*) [Magma G] (h : Equation17794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17795_implies_Equation2 (G : Type*) [Magma G] (h : Equation17795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17796_implies_Equation2 (G : Type*) [Magma G] (h : Equation17796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17798_implies_Equation2 (G : Type*) [Magma G] (h : Equation17798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17799_implies_Equation2 (G : Type*) [Magma G] (h : Equation17799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17800_implies_Equation2 (G : Type*) [Magma G] (h : Equation17800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17801_implies_Equation2 (G : Type*) [Magma G] (h : Equation17801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17803_implies_Equation2 (G : Type*) [Magma G] (h : Equation17803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17804_implies_Equation2 (G : Type*) [Magma G] (h : Equation17804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17805_implies_Equation2 (G : Type*) [Magma G] (h : Equation17805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17806_implies_Equation2 (G : Type*) [Magma G] (h : Equation17806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17808_implies_Equation2 (G : Type*) [Magma G] (h : Equation17808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17809_implies_Equation2 (G : Type*) [Magma G] (h : Equation17809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17810_implies_Equation2 (G : Type*) [Magma G] (h : Equation17810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17811_implies_Equation2 (G : Type*) [Magma G] (h : Equation17811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17812_implies_Equation2 (G : Type*) [Magma G] (h : Equation17812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17814_implies_Equation2 (G : Type*) [Magma G] (h : Equation17814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation17815_implies_Equation2 (G : Type*) [Magma G] (h : Equation17815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X5 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation17816_implies_Equation2 (G : Type*) [Magma G] (h : Equation17816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation17817_implies_Equation2 (G : Type*) [Magma G] (h : Equation17817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation17818_implies_Equation2 (G : Type*) [Magma G] (h : Equation17818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X0 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ X0) = X6 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation17820_implies_Equation2 (G : Type*) [Magma G] (h : Equation17820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17821_implies_Equation2 (G : Type*) [Magma G] (h : Equation17821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation17822_implies_Equation2 (G : Type*) [Magma G] (h : Equation17822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17823_implies_Equation2 (G : Type*) [Magma G] (h : Equation17823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17824_implies_Equation2 (G : Type*) [Magma G] (h : Equation17824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X1 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17826_implies_Equation2 (G : Type*) [Magma G] (h : Equation17826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17827_implies_Equation2 (G : Type*) [Magma G] (h : Equation17827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17828_implies_Equation2 (G : Type*) [Magma G] (h : Equation17828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17829_implies_Equation2 (G : Type*) [Magma G] (h : Equation17829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17830_implies_Equation2 (G : Type*) [Magma G] (h : Equation17830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X2 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17832_implies_Equation2 (G : Type*) [Magma G] (h : Equation17832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17833_implies_Equation2 (G : Type*) [Magma G] (h : Equation17833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17834_implies_Equation2 (G : Type*) [Magma G] (h : Equation17834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17835_implies_Equation2 (G : Type*) [Magma G] (h : Equation17835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17836_implies_Equation2 (G : Type*) [Magma G] (h : Equation17836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X3 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17838_implies_Equation2 (G : Type*) [Magma G] (h : Equation17838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17839_implies_Equation2 (G : Type*) [Magma G] (h : Equation17839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17840_implies_Equation2 (G : Type*) [Magma G] (h : Equation17840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17841_implies_Equation2 (G : Type*) [Magma G] (h : Equation17841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation17842_implies_Equation2 (G : Type*) [Magma G] (h : Equation17842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17844_implies_Equation2 (G : Type*) [Magma G] (h : Equation17844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17845_implies_Equation2 (G : Type*) [Magma G] (h : Equation17845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17846_implies_Equation2 (G : Type*) [Magma G] (h : Equation17846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17847_implies_Equation2 (G : Type*) [Magma G] (h : Equation17847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17848_implies_Equation2 (G : Type*) [Magma G] (h : Equation17848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation17849_implies_Equation2 (G : Type*) [Magma G] (h : Equation17849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X6)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18092_implies_Equation2 (G : Type*) [Magma G] (h : Equation18092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq10 eq10
  have eq21 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq14 eq11
  have eq33 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq21 eq10
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq10 eq33
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq101 eq48


@[equational_result]
theorem Equation18095_implies_Equation2 (G : Type*) [Magma G] (h : Equation18095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ X1) := superpose eq11 eq11
  have eq14 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ X1) := superpose eq13 eq12
  have eq20 (X0 X1 X3 : G) : (X1 ◇ X0) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X3))) := superpose eq18 eq10
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq11 eq20
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq18 eq28
  have eq44 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq20 eq14
  have eq50 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq44
  have eq53 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq50 eq36
  have eq56 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq53 eq14
  have eq76 (X0 X1 : G) : X0 = X1 := superpose eq11 eq56
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq85 eq76


@[equational_result]
theorem Equation18097_implies_Equation2 (G : Type*) [Magma G] (h : Equation18097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3))) = X0 := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X1) ◇ (X1 ◇ X0)))) := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1))) = X2 := superpose eq10 eq7
  have eq149 (X0 X1 : G) : (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq12
  have eq152 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq18 eq12
  have eq154 (X0 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq18 eq7
  have eq156 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)))) := superpose eq18 eq10
  have eq170 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X1 ◇ X0)))) := superpose eq7 eq152
  have eq175 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)))) := superpose eq18 eq152
  have eq186 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq152 eq152
  have eq187 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq18 eq152
  have eq191 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq152 eq7
  have eq202 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) := superpose eq152 eq10
  have eq205 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq152 eq10
  have eq284 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq10 eq186
  have eq287 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) := superpose eq11 eq186
  have eq305 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq186 eq18
  have eq312 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq152 eq284
  have eq327 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq152 eq14
  have eq334 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq186 eq14
  have eq345 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) := superpose eq186 eq14
  have eq346 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) := superpose eq9 eq14
  have eq366 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) ◇ X1) ◇ (((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = X1 := superpose eq14 eq152
  have eq376 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq312 eq334
  have eq377 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq376
  have eq382 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) := superpose eq346 eq287
  have eq385 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq18 eq377
  have eq417 (X0 X1 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq385 eq149
  have eq428 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq385 eq417
  have eq429 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq385 eq428
  have eq430 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq429 eq187
  have eq438 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq430 eq154
  have eq448 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq186 eq438
  have eq451 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq448 eq205
  have eq455 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq448 eq305
  have eq459 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq448 eq345
  have eq503 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq451 eq382
  have eq509 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0)))) := superpose eq451 eq156
  have eq514 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)))) := superpose eq451 eq175
  have eq517 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq451 eq191
  have eq519 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq451 eq327
  have eq525 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq448 eq455
  have eq528 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X0 := superpose eq525 eq459
  have eq529 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq448 eq528
  have eq530 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq529 eq503
  have eq533 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq529 eq530
  have eq536 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq533 eq429
  have eq561 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq536 eq519
  have eq562 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq533 eq561
  have eq576 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq562 eq517
  have eq581 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq576 eq202
  have eq582 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq533 eq581
  have eq584 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq582 eq170
  have eq599 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X0 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq582 eq509
  have eq632 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = X1 := superpose eq582 eq366
  have eq633 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq582 eq514
  have eq771 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = (X0 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X1 ◇ X0))) := superpose eq582 eq584
  have eq799 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq582 eq599
  have eq871 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq582 eq632
  have eq872 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq533 eq871
  have eq873 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq582 eq633
  have eq874 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq533 eq873
  have eq875 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq582 eq874
  have eq876 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq875 eq799
  have eq883 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X2) ◇ X1) := superpose eq876 eq771
  have eq895 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq883 eq872
  have eq961 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq883 eq895
  have eq962 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq582 eq961
  have eq963 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq962 eq385
  have eq969 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X0 := superpose eq963 eq883
  have eq978 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq963 eq969
  have eq979 (X0 X1 : G) : X0 = X1 := superpose eq448 eq978
  have eq987 (X0 : G) : sK0 ≠ X0 := superpose eq979 eq8
  subsumption eq987 eq979


@[equational_result]
theorem Equation18098_implies_Equation2 (G : Type*) [Magma G] (h : Equation18098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) ◇ X0) ◇ ((X1 ◇ X3) ◇ X3))) = X1 := superpose eq11 eq7
  have eq58 (X0 X1 X2 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = ((X2 ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq20 eq10
  have eq69 (X0 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq11 eq58
  have eq91 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X3) ◇ X3)) ◇ (X0 ◇ X1)) = ((X1 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X3) ◇ X3)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq10
  have eq99 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((((X3 ◇ ((X1 ◇ X4) ◇ X4)) ◇ X1) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X5) ◇ X5))))) = X1 := superpose eq9 eq20
  have eq100 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = (X0 ◇ X0) := superpose eq7 eq69
  have eq102 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq69 eq69
  have eq132 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq100 eq91
  have eq167 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq100 eq132
  have eq168 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = (X1 ◇ (X0 ◇ X1)) := superpose eq69 eq167
  have eq171 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((((X3 ◇ ((X1 ◇ X4) ◇ X4)) ◇ X1) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))))) = X1 := superpose eq168 eq99
  have eq195 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((((X3 ◇ ((X1 ◇ X4) ◇ X4)) ◇ X1) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1))) = X1 := superpose eq7 eq171
  have eq247 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq102 eq11
  have eq253 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1))) = X1 := superpose eq102 eq195
  have eq288 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq247 eq253
  have eq311 (X0 X2 : G) : X0 = X2 := superpose eq69 eq288
  have eq351 (X0 : G) : sK0 ≠ X0 := superpose eq311 eq8
  subsumption eq351 eq311


@[equational_result]
theorem Equation18099_implies_Equation2 (G : Type*) [Magma G] (h : Equation18099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq12 eq12
  have eq38 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq11 eq27
  have eq60 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq38 eq12
  have eq69 (X0 X2 : G) : X0 = X2 := superpose eq11 eq60
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq82 eq69


@[equational_result]
theorem Equation18102_implies_Equation2 (G : Type*) [Magma G] (h : Equation18102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq10 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq14 eq9
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq15 eq10
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq10 eq20
  have eq31 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq22 eq22
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq79 eq39


@[equational_result]
theorem Equation18105_implies_Equation2 (G : Type*) [Magma G] (h : Equation18105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq11 eq11
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq11
  have eq15 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq19 (X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq13 eq12
  have eq24 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq19 eq14
  have eq44 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose eq15 eq11
  have eq45 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq24 eq44
  have eq51 (X0 X1 : G) : X0 = X1 := superpose eq11 eq45
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq82 eq51


@[equational_result]
theorem Equation18107_implies_Equation2 (G : Type*) [Magma G] (h : Equation18107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq10 eq10
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0))) = X3 := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq10 eq7
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0))) = ((X1 ◇ ((X1 ◇ X3) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X4) ◇ X0))) := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq9
  have eq32 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0))))) = X3 := superpose eq9 eq7
  have eq37 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X4) ◇ (X1 ◇ X2)) = ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)))) ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq9 eq10
  have eq44 (X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X4) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq16 eq37
  have eq45 (X1 X2 X4 : G) : (X2 ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ X4) ◇ (X1 ◇ X2)) := superpose eq10 eq44
  have eq50 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ ((X1 ◇ X3) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X4) ◇ X0))) := superpose eq45 eq26
  have eq53 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) = X3 := superpose eq45 eq32
  have eq97 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = ((X0 ◇ X3) ◇ X0) := superpose eq7 eq45
  have eq129 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X4) ◇ X0) := superpose eq97 eq97
  have eq146 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (((X2 ◇ X3) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))))) = X0 := superpose eq97 eq10
  have eq152 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2)))) = ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2)))) := superpose eq97 eq31
  have eq170 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2)))) = ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (((X2 ◇ X3) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2)))) := superpose eq45 eq152
  have eq181 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X4 ◇ ((X4 ◇ X5) ◇ X4)) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))))) = X0 := superpose eq97 eq13
  have eq220 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X4 ◇ X2) ◇ (X2 ◇ (X4 ◇ X2))))) = X0 := superpose eq50 eq181
  have eq265 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) := superpose eq129 eq45
  have eq266 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := superpose eq129 eq10
  have eq323 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (((X0 ◇ X3) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X3) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))))) = X2 := superpose eq31 eq53
  have eq400 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)))))) = X3 := superpose eq265 eq53
  have eq447 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) = X3 := superpose eq12 eq400
  have eq448 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2)))) := superpose eq447 eq170
  have eq449 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := superpose eq447 eq146
  have eq451 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (((X0 ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq448 eq323
  have eq456 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq449 eq451
  have eq497 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X4 ◇ X2) ◇ (X2 ◇ (X4 ◇ X2))))) = X0 := superpose eq456 eq220
  have eq505 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := superpose eq456 eq266
  have eq561 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X2) ◇ (X2 ◇ (X4 ◇ X2))))) = X0 := superpose eq456 eq497
  have eq564 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq505 eq561
  have eq598 (X0 X3 : G) : X0 = X3 := superpose eq10 eq564
  have eq685 (X0 : G) : sK0 ≠ X0 := superpose eq598 eq8
  subsumption eq685 eq598


@[equational_result]
theorem Equation18109_implies_Equation2 (G : Type*) [Magma G] (h : Equation18109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq39 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq14 eq14
  have eq58 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq39 eq14
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq11 eq58
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq74 eq65


@[equational_result]
theorem Equation18111_implies_Equation2 (G : Type*) [Magma G] (h : Equation18111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X2)) = ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ X0) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose eq7 eq11
  have eq17 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X0) = ((X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq11 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq7 eq10
  have eq37 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))))) := superpose eq10 eq25
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X0 ◇ ((X3 ◇ X2) ◇ X0)) := superpose eq25 eq25
  have eq51 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := superpose eq25 eq7
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X4 ◇ (X2 ◇ X4))) ◇ ((X5 ◇ (X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3))) ◇ (X3 ◇ (X4 ◇ (X2 ◇ X4)))))) := superpose eq10 eq9
  have eq117 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ ((X4 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) ◇ X1)) := superpose eq7 eq48
  have eq120 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) = (X3 ◇ ((X5 ◇ ((X4 ◇ X2) ◇ X0)) ◇ X3)) := superpose eq48 eq48
  have eq125 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) := superpose eq7 eq48
  have eq126 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq10 eq48
  have eq127 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ X0) = (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X3 ◇ X0) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0))) := superpose eq11 eq48
  have eq130 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))))) = (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X4 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq25 eq48
  have eq161 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))))) := superpose eq48 eq10
  have eq164 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X0) = ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X4 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X0))) := superpose eq48 eq7
  have eq173 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X0)) = ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq48 eq25
  have eq174 (X0 X1 X2 X3 X4 : G) : ((((X4 ◇ X3) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X4 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))))) = X1 := superpose eq48 eq7
  have eq177 (X0 X1 X2 X3 X4 : G) : (((((X4 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))) ◇ X1) ◇ ((((X4 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))) ◇ X1)) = X1 := superpose eq48 eq11
  have eq209 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X4 ◇ (X2 ◇ X4))) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X4 ◇ (X2 ◇ X4)))))) := superpose eq117 eq77
  have eq295 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq48 eq51
  have eq304 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X2 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq51 eq48
  have eq407 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X0) ◇ X1)) = (X1 ◇ ((X4 ◇ (X5 ◇ (X0 ◇ X5))) ◇ X1)) := superpose eq11 eq117
  have eq408 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X0) ◇ X0) ◇ X1)) = (X1 ◇ ((X4 ◇ (X5 ◇ (X0 ◇ X5))) ◇ X1)) := superpose eq14 eq117
  have eq409 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (((X4 ◇ X2) ◇ X0) ◇ X3)) = (X3 ◇ ((X5 ◇ (X6 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X6))) ◇ X3)) := superpose eq48 eq117
  have eq442 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) ◇ (X3 ◇ ((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))))) = (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ ((X4 ◇ X5) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))))) := superpose eq48 eq117
  have eq473 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X4 ◇ ((X5 ◇ X1) ◇ X4))) ◇ X0)) ◇ X0)) = (((X3 ◇ (X4 ◇ ((X5 ◇ X1) ◇ X4))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (((X3 ◇ (X4 ◇ ((X5 ◇ X1) ◇ X4))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq117 eq25
  have eq476 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq117 eq51
  have eq575 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X4)) = (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3))) ◇ (X3 ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)))))) := superpose eq17 eq10
  have eq586 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X4 ◇ (X2 ◇ X4))) ◇ ((X4 ◇ (X2 ◇ X4)) ◇ (X3 ◇ (X4 ◇ (X2 ◇ X4)))))) = (X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ X3)) := superpose eq17 eq25
  have eq590 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ ((X4 ◇ (X2 ◇ X4)) ◇ X3)) = (X3 ◇ ((X5 ◇ (X6 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ X6))) ◇ X3)) := superpose eq17 eq117
  have eq598 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X3 ◇ ((X4 ◇ (X2 ◇ X4)) ◇ X3)) := superpose eq117 eq590
  have eq602 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ X3)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X4 ◇ (X2 ◇ X4))) ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ X4)))))) := superpose eq598 eq586
  have eq611 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))))) := superpose eq598 eq37
  have eq623 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X4 ◇ (X2 ◇ X4))) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X4 ◇ (X2 ◇ X4)))))) = (X3 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq598 eq209
  have eq641 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (((X4 ◇ X2) ◇ X0) ◇ X3)) = (X3 ◇ ((X5 ◇ (X6 ◇ ((X1 ◇ X2) ◇ X6))) ◇ X3)) := superpose eq598 eq409
  have eq679 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X3 ◇ (((X4 ◇ X2) ◇ X0) ◇ X3)) := superpose eq117 eq641
  have eq680 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq679 eq476
  have eq681 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X4 ◇ ((X5 ◇ X1) ◇ X4))) ◇ X0)) ◇ X0)) = (((X3 ◇ (X4 ◇ ((X5 ◇ X1) ◇ X4))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X4 ◇ ((X5 ◇ X1) ◇ X4)) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq679 eq473
  have eq682 (X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X4 ◇ (X2 ◇ X4))) ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ X4)))))) = (X3 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq679 eq623
  have eq699 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ ((X4 ◇ (X5 ◇ (X0 ◇ X5))) ◇ X1)) := superpose eq679 eq408
  have eq710 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X4 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq598 eq680
  have eq711 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X4 ◇ ((X5 ◇ X1) ◇ X4))) ◇ X0)) ◇ X0)) = (((X3 ◇ (X4 ◇ ((X5 ◇ X1) ◇ X4))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X5 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq598 eq681
  have eq716 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X0) ◇ X1)) := superpose eq699 eq407
  have eq732 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X4 ◇ (X2 ◇ X4))) ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ X4)))))) := superpose eq716 eq602
  have eq733 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = (X3 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq732 eq682
  have eq736 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))))) = ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq733 eq161
  have eq737 (X0 X1 X3 X4 : G) : ((((X4 ◇ X3) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X4 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))))) = X1 := superpose eq733 eq174
  have eq739 (X0 X1 X3 X4 : G) : (((((X4 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X1) ◇ ((((X4 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X1)) = X1 := superpose eq733 eq177
  have eq751 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X4 ◇ ((X5 ◇ X1) ◇ X4))) ◇ X0)) ◇ X0)) = (((X3 ◇ (X4 ◇ ((X5 ◇ X1) ◇ X4))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq733 eq711
  have eq752 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq733 eq710
  have eq755 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq733 eq295
  have eq756 (X0 X1 X2 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X0)) = ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq733 eq173
  have eq760 (X0 X1 X2 X3 X5 X6 : G) : (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) ◇ (X3 ◇ ((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))))) = (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ (X5 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))))) := superpose eq733 eq442
  have eq764 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq733 eq7
  have eq773 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq733 eq25
  have eq786 (X0 X2 X3 X4 X5 : G) : (X3 ◇ ((X5 ◇ ((X4 ◇ X2) ◇ X0)) ◇ X3)) = (X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) := superpose eq733 eq120
  have eq787 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq733 eq125
  have eq788 (X0 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X2 ◇ X3)))) := superpose eq733 eq126
  have eq789 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X3 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq733 eq127
  have eq790 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X4 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2)))) = (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq733 eq130
  have eq793 (X0 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X0) = ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X4 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X0))) := superpose eq733 eq164
  have eq844 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3))) ◇ (X3 ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)))))) := superpose eq733 eq575
  have eq846 (X0 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) = ((X0 ◇ (X2 ◇ X0)) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq733 eq611
  have eq884 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3))) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))))) := superpose eq733 eq736
  have eq889 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X4 ◇ (X1 ◇ X4))) ◇ X0)) ◇ X0)) = (((X3 ◇ (X4 ◇ (X1 ◇ X4))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq733 eq751
  have eq890 (X0 X1 X3 X4 : G) : (((X3 ◇ (X4 ◇ (X1 ◇ X4))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = (X0 ◇ (((X3 ◇ (X4 ◇ (X1 ◇ X4))) ◇ X0) ◇ X0)) := superpose eq733 eq889
  have eq891 (X0 X1 X3 X4 : G) : (X0 ◇ (X0 ◇ X0)) = (((X3 ◇ (X4 ◇ (X1 ◇ X4))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq733 eq890
  have eq892 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq733 eq752
  have eq893 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X0) := superpose eq891 eq892
  have eq898 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq733 eq756
  have eq899 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq733 eq898
  have eq900 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq899 eq755
  have eq901 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X0) := superpose eq900 eq893
  have eq907 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X2 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))))) = (X0 ◇ X0) := superpose eq901 eq304
  have eq913 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X3 ◇ X1)) = X1 := superpose eq901 eq739
  have eq923 (X0 X1 X2 X3 X5 X6 : G) : (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) ◇ (X3 ◇ ((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))))) = (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) ◇ ((X2 ◇ X3) ◇ (X5 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))))) := superpose eq901 eq760
  have eq924 (X0 X1 X2 X3 X5 X6 : G) : (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X3 ◇ ((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) = (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ ((X2 ◇ X3) ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) := superpose eq733 eq923
  have eq937 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq773 eq907
  have eq951 (X0 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = (X3 ◇ ((X5 ◇ ((X4 ◇ X2) ◇ X0)) ◇ X3)) := superpose eq598 eq786
  have eq952 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq937 eq787
  have eq956 (X0 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) = ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq901 eq788
  have eq957 (X0 X3 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq952 eq789
  have eq958 (X0 X2 X3 : G) : ((X3 ◇ X2) ◇ X0) = ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq951 eq793
  have eq959 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X2) ◇ X0) := superpose eq913 eq958
  have eq960 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq959 eq957
  have eq967 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X4 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2)))) = (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq959 eq790
  have eq978 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X4 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))))) = X1 := superpose eq959 eq737
  have eq986 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3))) = (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq959 eq884
  have eq992 (X0 X1 X3 X5 X6 : G) : (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X3 ◇ ((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) = (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) := superpose eq959 eq924
  have eq994 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq959 eq937
  have eq1003 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq959 eq960
  have eq1004 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq764 eq1003
  have eq1017 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X4 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2)))) = (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq959 eq967
  have eq1018 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X4 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq959 eq1017
  have eq1019 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq959 eq1018
  have eq1042 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))))) = X1 := superpose eq959 eq978
  have eq1043 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))))) = X1 := superpose eq959 eq1042
  have eq1044 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1))))) = X1 := superpose eq959 eq1043
  have eq1045 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1))))) = X1 := superpose eq959 eq1044
  have eq1046 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1))))) = X1 := superpose eq1004 eq1045
  have eq1064 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3))) = (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq959 eq986
  have eq1065 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3))) = (((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq959 eq1064
  have eq1066 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3))) = (((X2 ◇ X3) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq959 eq1065
  have eq1067 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3))) = ((X3 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq959 eq1066
  have eq1068 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X3))) = ((X3 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq959 eq1067
  have eq1081 (X0 X1 X3 X5 X6 : G) : (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X3 ◇ ((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) = ((X0 ◇ (X1 ◇ (X3 ◇ X1))) ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) := superpose eq959 eq992
  have eq1082 (X0 X1 X3 X5 X6 : G) : (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X3 ◇ ((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) = ((X1 ◇ (X3 ◇ X1)) ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) := superpose eq959 eq1081
  have eq1083 (X0 X1 X3 X5 X6 : G) : (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X3 ◇ ((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) = ((X3 ◇ X1) ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) := superpose eq959 eq1082
  have eq1084 (X0 X1 X3 X5 X6 : G) : (((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X3 ◇ ((X6 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) = (X1 ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) := superpose eq959 eq1083
  have eq1085 (X0 X1 X3 X5 : G) : (X1 ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) = ((X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) := superpose eq959 eq1084
  have eq1095 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq1004 eq994
  have eq1096 (X0 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq1095 eq956
  have eq1250 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)))))) := superpose eq959 eq844
  have eq1251 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)))))) := superpose eq959 eq1250
  have eq1252 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X3 ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X2 ◇ X3)))))) := superpose eq959 eq1251
  have eq1253 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X3 ◇ (X4 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X3)))))) := superpose eq959 eq1252
  have eq1254 (X0 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = ((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X3)))))) := superpose eq959 eq1253
  have eq1262 (X0 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) = ((X0 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq959 eq846
  have eq1263 (X0 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) = ((X0 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq959 eq1262
  have eq1264 (X0 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) = ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq959 eq1263
  have eq1265 (X0 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) = ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq959 eq1264
  have eq1266 (X0 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) = ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq959 eq1265
  have eq1267 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq1254 eq1266
  have eq1268 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X2 := superpose eq1096 eq1267
  have eq1269 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq1268 eq1019
  have eq1271 (X0 X1 X3 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) = (X1 ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))))) := superpose eq1268 eq1085
  have eq1317 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq1268 eq1269
  have eq1318 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq1268 eq1317
  have eq1321 (X0 X1 X3 X5 : G) : (X5 ◇ (X0 ◇ X1)) = (X1 ◇ (X3 ◇ (X5 ◇ (X0 ◇ X1)))) := superpose eq1268 eq1271
  have eq1322 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = X1 := superpose eq1321 eq1046
  have eq1323 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X2 ◇ X3))) = ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := superpose eq1321 eq1068
  have eq1325 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X3 ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq1322 eq1323
  have eq1326 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X3 := superpose eq1322 eq1325
  have eq1328 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq1326 eq1318
  have eq1331 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq1328 eq913
  have eq1336 (X0 X2 : G) : X0 = X2 := superpose eq1331 eq1331
  have eq1356 (X0 : G) : sK0 ≠ X0 := superpose eq1336 eq8
  subsumption eq1356 eq1336


@[equational_result]
theorem Equation18113_implies_Equation2 (G : Type*) [Magma G] (h : Equation18113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq11 eq11
  have eq19 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq14 eq12
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq19 eq11
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq11 eq26
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq98 eq32


@[equational_result]
theorem Equation18115_implies_Equation2 (G : Type*) [Magma G] (h : Equation18115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq11
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq12
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq12
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) ◇ ((X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)))) := superpose eq12 eq7
  have eq22 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq17
  have eq23 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) = (X3 ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) ◇ ((X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3)))) := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = (X3 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ ((X4 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)))) := superpose eq12 eq9
  have eq28 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (X2 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)))) := superpose eq12 eq9
  have eq31 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) := superpose eq12 eq9
  have eq41 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9
  have eq43 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))))) = X3 := superpose eq9 eq7
  have eq47 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = ((X0 ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) ◇ ((X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)))) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq9 eq12
  have eq52 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq21 eq23
  have eq57 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq28 eq24
  have eq61 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq57 eq31
  have eq68 (X1 X2 X4 : G) : ((X4 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = (((X2 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq21 eq47
  have eq144 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq7 eq22
  have eq145 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq41 eq22
  have eq147 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq22
  have eq178 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq144 eq145
  have eq179 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq7 eq178
  have eq182 (X1 X2 X4 : G) : ((X4 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = ((((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq28 eq147
  have eq183 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X2) = ((X4 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq22 eq182
  have eq184 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq183 eq179
  have eq206 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq7 eq184
  have eq239 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq52 eq206
  have eq240 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq239 eq68
  have eq244 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X3 := superpose eq239 eq43
  have eq257 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq240 eq61
  have eq260 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq257 eq9
  have eq272 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq244 eq257
  have eq274 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq272 eq7
  have eq276 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq272 eq13
  have eq283 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X0 ◇ X1) := superpose eq272 eq239
  have eq284 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq272 eq260
  have eq292 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X1 := superpose eq276 eq240
  have eq309 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq292 eq283
  have eq310 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq309 eq274
  have eq322 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq309 eq284
  have eq323 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq309 eq322
  have eq405 (X0 X1 : G) : X0 = X1 := superpose eq310 eq323
  have eq410 (X0 : G) : sK0 ≠ X0 := superpose eq405 eq8
  subsumption eq410 eq405


@[equational_result]
theorem Equation18117_implies_Equation2 (G : Type*) [Magma G] (h : Equation18117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ X5))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ X1) := superpose eq11 eq11
  have eq19 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X1 ◇ X1) := superpose eq13 eq12
  have eq21 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ X4) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X5))) = X4 := superpose eq19 eq10
  have eq27 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X4))) := superpose eq21 eq21
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X1 := superpose eq11 eq21
  have eq35 (X0 X1 X2 X3 : G) : ((((X2 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq21 eq11
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ (X3 ◇ X4))) := superpose eq11 eq27
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq28 eq36
  have eq40 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq37 eq35
  have eq41 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq40 eq13
  have eq42 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq41
  have eq62 (X0 X1 : G) : X0 = X1 := superpose eq11 eq42
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq106 eq62


@[equational_result]
theorem Equation18119_implies_Equation2 (G : Type*) [Magma G] (h : Equation18119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X4 ◇ X4) ◇ (X1 ◇ X0)))) := superpose eq10 eq7
  have eq32 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) = X2 := superpose eq12 eq10
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)))) := superpose eq12 eq7
  have eq50 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq17 eq17
  have eq109 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X0 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)))) ◇ (X1 ◇ X1)) := superpose eq9 eq12
  have eq118 (X1 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq36 eq109
  have eq122 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ X0) := superpose eq7 eq50
  have eq140 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq122 eq9
  have eq141 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq122 eq25
  have eq173 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq122 eq140
  have eq174 (X1 X2 X3 : G) : (X1 ◇ X1) = (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X1)) := superpose eq173 eq141
  have eq177 (X2 X3 : G) : ((X2 ◇ X3) ◇ (X2 ◇ X2)) = X3 := superpose eq174 eq10
  have eq190 (X1 X3 : G) : ((X3 ◇ X3) ◇ X1) = X1 := superpose eq177 eq118
  have eq201 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq190 eq32
  have eq208 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq190 eq201
  have eq209 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq208 eq177
  have eq215 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq208 eq209
  have eq218 (X0 X2 : G) : X0 = X2 := superpose eq215 eq215
  have eq220 (X0 : G) : sK0 ≠ X0 := superpose eq218 eq8
  subsumption eq220 eq218


@[equational_result]
theorem Equation18120_implies_Equation2 (G : Type*) [Magma G] (h : Equation18120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X3) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X0) ◇ X0))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ ((((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X3 ◇ X3) ◇ X3))) = X0 := superpose eq7 eq9
  have eq37 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2))) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2))) ◇ ((X1 ◇ X1) ◇ X1))) ◇ X3) ◇ X4) ◇ X3) = X4 := superpose eq9 eq11
  have eq46 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ X4) = ((X0 ◇ ((((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) ◇ X0) ◇ ((X3 ◇ X3) ◇ X3))) ◇ X2) := superpose eq9 eq11
  have eq54 (X1 X3 X4 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X3) ◇ X4) ◇ X3) = X4 := superpose eq7 eq37
  have eq55 (X2 X4 : G) : (X2 ◇ X2) = ((X4 ◇ X4) ◇ X4) := superpose eq15 eq46
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) = X1 := superpose eq55 eq7
  have eq75 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) = X2 := superpose eq55 eq11
  have eq91 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = X2 := superpose eq65 eq10
  have eq115 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq91 eq75
  have eq116 (X3 X4 : G) : (X3 ◇ X3) = X4 := superpose eq115 eq54
  have eq204 (X0 X2 : G) : X0 = X2 := superpose eq116 eq116
  have eq206 (X0 : G) : sK0 ≠ X0 := superpose eq204 eq8
  subsumption eq206 eq204


@[equational_result]
theorem Equation18121_implies_Equation2 (G : Type*) [Magma G] (h : Equation18121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq12 eq12
  have eq35 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq11 eq28
  have eq108 (X0 X2 : G) : X0 = X2 := superpose eq11 eq35
  have eq253 (X0 : G) : sK0 ≠ X0 := superpose eq108 eq8
  subsumption eq253 eq108


@[equational_result]
theorem Equation18123_implies_Equation2 (G : Type*) [Magma G] (h : Equation18123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq10 eq12
  have eq31 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq12 eq7
  have eq33 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0)))) := superpose eq12 eq10
  have eq39 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq26 eq33
  have eq40 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X0) := superpose eq31 eq39
  have eq43 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq7 eq40
  have eq129 (X0 X2 : G) : X0 = X2 := superpose eq43 eq43
  have eq238 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq238 eq129


@[equational_result]
theorem Equation18124_implies_Equation2 (G : Type*) [Magma G] (h : Equation18124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X0) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X5) ◇ (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X4) ◇ X3))) = X5 := superpose eq7 eq11
  have eq31 (X0 X1 X2 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) = X4 := superpose eq11 eq11
  have eq43 (X0 X1 X5 : G) : ((X0 ◇ X5) ◇ X1) = X5 := superpose eq31 eq29
  have eq51 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq43 eq18
  have eq58 (X0 X2 : G) : X0 = X2 := superpose eq51 eq51
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq80 eq58


@[equational_result]
theorem Equation18125_implies_Equation2 (G : Type*) [Magma G] (h : Equation18125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq11
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq45 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ ((((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4) ◇ X0) ◇ (X5 ◇ ((X6 ◇ X7) ◇ X7)))) = X4 := superpose eq12 eq11
  have eq119 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) = X4 := superpose eq7 eq21
  have eq155 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq119 eq45
  have eq188 (X0 X2 : G) : X0 = X2 := superpose eq19 eq155
  have eq197 (X0 : G) : sK0 ≠ X0 := superpose eq188 eq8
  subsumption eq197 eq188


@[equational_result]
theorem Equation18126_implies_Equation2 (G : Type*) [Magma G] (h : Equation18126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq39 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq15 eq15
  have eq58 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq39 eq15
  have eq66 (X0 X2 : G) : X0 = X2 := superpose eq11 eq58
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq83 eq66


@[equational_result]
theorem Equation18128_implies_Equation2 (G : Type*) [Magma G] (h : Equation18128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X3 ◇ (((X2 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)))) = X1 := superpose eq11 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq7
  have eq21 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0)))) = X1 := superpose eq18 eq17
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X0 ◇ (X3 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose eq18 eq9
  have eq27 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X1 := superpose eq18 eq21
  have eq28 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq27 eq24
  have eq29 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq27 eq28
  have eq31 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq29 eq12
  have eq36 (X0 X1 : G) : X0 = X1 := superpose eq29 eq31
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq38 eq36


@[equational_result]
theorem Equation18129_implies_Equation2 (G : Type*) [Magma G] (h : Equation18129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X3 ◇ (((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2)))) := superpose eq7 eq11
  have eq15 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq11 eq7
  have eq18 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq11 eq16
  have eq53 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) := superpose eq11 eq9
  have eq66 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq15 eq53
  have eq67 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq18 eq66
  have eq81 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq67
  have eq83 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq67 eq7
  have eq90 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq81 eq83
  have eq91 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq90 eq67
  have eq95 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq91 eq12
  have eq98 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq91 eq18
  have eq109 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq91 eq95
  have eq110 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X0 := superpose eq98 eq109
  have eq142 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq90 eq110
  have eq143 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq91 eq142
  have eq145 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq143 eq110
  have eq148 (X0 X2 : G) : X0 = X2 := superpose eq145 eq145
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq148 eq8
  subsumption eq153 eq148


@[equational_result]
theorem Equation18130_implies_Equation2 (G : Type*) [Magma G] (h : Equation18130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq67 eq21


@[equational_result]
theorem Equation18132_implies_Equation2 (G : Type*) [Magma G] (h : Equation18132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq11
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq7
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq15 eq20
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq72 eq56


@[equational_result]
theorem Equation18133_implies_Equation2 (G : Type*) [Magma G] (h : Equation18133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X3 ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X0))) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ X1)) = X0 := superpose eq11 eq11
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X2) ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq11 eq7
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X3))) := superpose eq11 eq10
  have eq28 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = (((X3 ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X4 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X0)) := superpose eq7 eq10
  have eq71 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X3) ◇ (X3 ◇ X0)) ◇ X1)) = (((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X3) ◇ (X4 ◇ (((X1 ◇ ((((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X3) ◇ (X3 ◇ X0)) ◇ X1)) ◇ X0) ◇ X4))) := superpose eq11 eq9
  have eq105 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = ((X3 ◇ ((X1 ◇ X0) ◇ X3)) ◇ ((X4 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X3))))) := superpose eq10 eq12
  have eq127 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X3 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq12
  have eq167 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = ((X3 ◇ ((X1 ◇ X0) ◇ X3)) ◇ ((X4 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X4)) ◇ X1)) := superpose eq7 eq105
  have eq192 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (((X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq15 eq12
  have eq260 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ X3)) := superpose eq127 eq11
  have eq308 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq260 eq167
  have eq468 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = (X4 ◇ ((((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4)) := superpose eq17 eq127
  have eq500 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ X1) = (X4 ◇ ((((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4)) := superpose eq308 eq468
  have eq502 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X0) = (((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X3) ◇ (X4 ◇ ((((X0 ◇ X3) ◇ X0) ◇ X0) ◇ X4))) := superpose eq500 eq71
  have eq769 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ X0) := superpose eq11 eq308
  have eq775 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq308 eq7
  have eq1520 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) = (((X4 ◇ (((X3 ◇ (X1 ◇ X3)) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X4)) ◇ (X3 ◇ (X1 ◇ X3))) ◇ (X5 ◇ ((((X0 ◇ X1) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X5))) := superpose eq23 eq502
  have eq1618 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) := superpose eq308 eq769
  have eq1635 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq769 eq7
  have eq1824 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq308 eq775
  have eq1875 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq775 eq1824
  have eq1878 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ (((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) ◇ X0)) ◇ X1)) := superpose eq1875 eq192
  have eq1884 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) = X0 := superpose eq1875 eq1618
  have eq1889 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq1875 eq1635
  have eq1898 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0)) ◇ X1)) = X0 := superpose eq1875 eq1878
  have eq1905 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq1875 eq1889
  have eq1907 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq1905 eq1898
  have eq1909 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq1875 eq1907
  have eq1917 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) = (((X4 ◇ (((X3 ◇ (X1 ◇ X3)) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X4)) ◇ (X3 ◇ (X1 ◇ X3))) ◇ (X5 ◇ (((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X5))) := superpose eq1909 eq1520
  have eq1918 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq1909 eq7
  have eq1920 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq1909 eq11
  have eq1927 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = (((X3 ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq1909 eq28
  have eq2325 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) = (((X4 ◇ (((X3 ◇ (X1 ◇ X3)) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X4)) ◇ (X3 ◇ (X1 ◇ X3))) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq1909 eq1917
  have eq2326 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (((X4 ◇ (((X3 ◇ (X1 ◇ X3)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X4)) ◇ (X3 ◇ (X1 ◇ X3))) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq1909 eq2325
  have eq2327 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (((X4 ◇ ((X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X4)) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq1909 eq2326
  have eq2328 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (((X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq1909 eq2327
  have eq2352 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((((X2 ◇ X0) ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq1909 eq1927
  have eq2353 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq1918 eq2352
  have eq2357 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq2353 eq1884
  have eq2363 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq1875 eq2357
  have eq2364 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq1909 eq2363
  have eq2365 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq2364 eq2328
  have eq2366 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq2364 eq1920
  have eq2380 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq2364 eq2365
  have eq2381 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq2364 eq2380
  have eq2382 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq2364 eq2381
  have eq2383 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq2364 eq2382
  have eq2384 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq2364 eq2366
  have eq2973 (X0 X1 : G) : X0 = X1 := superpose eq2384 eq2383
  have eq2978 (X0 : G) : sK0 ≠ X0 := superpose eq2973 eq8
  subsumption eq2978 eq2973


@[equational_result]
theorem Equation18134_implies_Equation2 (G : Type*) [Magma G] (h : Equation18134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq71 eq23


@[equational_result]
theorem Equation18138_implies_Equation2 (G : Type*) [Magma G] (h : Equation18138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation18140_implies_Equation2 (G : Type*) [Magma G] (h : Equation18140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ (X1 ◇ X0)) = X5 := superpose eq7 eq12
  have eq15 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ X1) = X4 := superpose eq7 eq12
  have eq23 (X0 X1 X4 X5 : G) : (X4 ◇ (X1 ◇ X0)) = X5 := superpose eq15 eq13
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq15 eq23
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq60 eq43


@[equational_result]
theorem Equation18141_implies_Equation2 (G : Type*) [Magma G] (h : Equation18141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq20 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (X0 ◇ (X3 ◇ (((X0 ◇ X2) ◇ X4) ◇ X3))) := superpose eq12 eq7
  have eq24 (X0 X1 X2 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (X0 ◇ (X4 ◇ (((X0 ◇ X2) ◇ X1) ◇ X4))) := superpose eq7 eq10
  have eq26 (X0 X1 X2 X4 : G) : (X2 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ (X4 ◇ ((X1 ◇ X2) ◇ X4))) := superpose eq10 eq10
  have eq33 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((X4 ◇ (X1 ◇ X4)) ◇ (X0 ◇ X1))) = X3 := superpose eq10 eq7
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq20 eq24
  have eq49 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X2)) := superpose eq39 eq26
  have eq50 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = X1 := superpose eq12 eq49
  have eq55 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ (X0 ◇ X1))) = X3 := superpose eq50 eq33
  have eq56 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X3 := superpose eq50 eq55
  have eq68 (X0 X2 : G) : X0 = X2 := superpose eq50 eq56
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq73 eq68


@[equational_result]
theorem Equation18142_implies_Equation2 (G : Type*) [Magma G] (h : Equation18142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq45 eq30


@[equational_result]
theorem Equation18143_implies_Equation2 (G : Type*) [Magma G] (h : Equation18143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq16
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq66 eq22


@[equational_result]
theorem Equation18145_implies_Equation2 (G : Type*) [Magma G] (h : Equation18145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq7
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq13 eq7
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq13 eq16
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq21 eq35
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq89 eq40


@[equational_result]
theorem Equation18146_implies_Equation2 (G : Type*) [Magma G] (h : Equation18146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X4 ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4))) := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X0) ◇ X3) ◇ (X5 ◇ (((X4 ◇ X0) ◇ X3) ◇ X5))) = (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) = ((X3 ◇ X0) ◇ ((X4 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X0)) := superpose eq7 eq9
  have eq30 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) = X0 := superpose eq10 eq18
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) := superpose eq30 eq11
  have eq50 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X1)) = (((X3 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ (X4 ◇ (((X3 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ X4))) := superpose eq10 eq9
  have eq56 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq50
  have eq59 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = ((X2 ◇ X0) ◇ X0) := superpose eq56 eq14
  have eq61 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ X3) := superpose eq56 eq31
  have eq68 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = (((X4 ◇ X0) ◇ X3) ◇ ((X4 ◇ X0) ◇ X3)) := superpose eq56 eq12
  have eq79 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq56 eq59
  have eq83 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq56 eq61
  have eq84 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq83 eq79
  have eq92 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = (X0 ◇ X0) := superpose eq83 eq68
  have eq93 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = X0 := superpose eq84 eq92
  have eq94 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq83 eq93
  have eq95 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq56 eq94
  have eq96 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq95 eq56
  have eq120 (X0 X2 : G) : X0 = X2 := superpose eq96 eq96
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq120 eq8
  subsumption eq133 eq120


@[equational_result]
theorem Equation18147_implies_Equation2 (G : Type*) [Magma G] (h : Equation18147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq11 eq14
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq66 eq20


@[equational_result]
theorem Equation18149_implies_Equation2 (G : Type*) [Magma G] (h : Equation18149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (X0 ◇ X2) := superpose eq7 eq11
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq7
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) = (X2 ◇ X1) := superpose eq19 eq9
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ X0)) := superpose eq19 eq15
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq19 eq24
  have eq43 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X4) := superpose eq31 eq19
  have eq51 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = X1 := superpose eq19 eq43
  have eq53 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq51 eq30
  have eq61 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq53 eq19
  have eq66 (X0 X3 : G) : X0 = X3 := superpose eq61 eq61
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq85 eq66


@[equational_result]
theorem Equation18151_implies_Equation2 (G : Type*) [Magma G] (h : Equation18151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq71 eq23


@[equational_result]
theorem Equation18153_implies_Equation2 (G : Type*) [Magma G] (h : Equation18153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ ((X1 ◇ X3) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X2 ◇ X0))) = ((X3 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X4 ◇ ((X0 ◇ X4) ◇ X0))) := superpose eq7 eq9
  have eq22 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq9 eq9
  have eq49 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ (X2 ◇ X0))) = (X3 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X2 ◇ X0))) := superpose eq7 eq22
  have eq72 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X2))) := superpose eq22 eq7
  have eq93 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X2 ◇ X0))) = ((X2 ◇ X0) ◇ X2) := superpose eq72 eq18
  have eq115 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ (X2 ◇ X0))) = ((X2 ◇ X0) ◇ X2) := superpose eq93 eq49
  have eq132 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq115 eq10
  have eq167 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq132
  have eq179 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq7 eq167
  have eq180 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0)))) = (X1 ◇ (X2 ◇ X1)) := superpose eq167 eq167
  have eq189 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq167 eq167
  have eq230 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq167 eq189
  have eq232 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq189
  have eq239 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq189 eq93
  have eq249 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq232 eq7
  have eq252 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X2))) := superpose eq232 eq72
  have eq262 (X0 X1 X3 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq232 eq179
  have eq270 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq232 eq252
  have eq276 (X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ (X2 ◇ X1)) := superpose eq262 eq180
  have eq284 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) = X2 := superpose eq276 eq230
  have eq295 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq276 eq239
  have eq296 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq284 eq295
  have eq298 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq296 eq270
  have eq302 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X2 ◇ X0))) = X0 := superpose eq298 eq93
  have eq317 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq298 eq302
  have eq331 (X0 X1 : G) : X0 = X1 := superpose eq249 eq317
  have eq353 (X0 : G) : sK0 ≠ X0 := superpose eq331 eq8
  subsumption eq353 eq331


@[equational_result]
theorem Equation18154_implies_Equation2 (G : Type*) [Magma G] (h : Equation18154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ X3) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ ((X1 ◇ X3) ◇ X3)) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq9
  have eq26 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)))) = X3 := superpose eq9 eq7
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq11
  have eq53 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X1) := superpose eq42 eq42
  have eq59 (X0 X1 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq42 eq7
  have eq60 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) := superpose eq42 eq7
  have eq71 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X5) ◇ X5)) ◇ (((X3 ◇ ((X1 ◇ X3) ◇ X3)) ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X3)))) ◇ (X5 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X5) ◇ X5))))) = X4 := superpose eq10 eq10
  have eq178 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X4 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)))) := superpose eq25 eq26
  have eq209 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X2 := superpose eq26 eq10
  have eq244 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) ◇ X2) ◇ (((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)))) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)))))) = X2 := superpose eq26 eq59
  have eq285 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) ◇ X2) ◇ ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1))) = X2 := superpose eq178 eq244
  have eq286 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) ◇ X2) ◇ X1) = X2 := superpose eq209 eq285
  have eq287 (X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X2 := superpose eq60 eq286
  have eq415 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X2 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) ◇ X2))) := superpose eq287 eq9
  have eq421 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ X2))) = X1 := superpose eq287 eq7
  have eq461 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq421 eq415
  have eq462 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq461 eq42
  have eq463 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = (X1 ◇ X1) := superpose eq461 eq53
  have eq565 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq461 eq462
  have eq567 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := superpose eq461 eq463
  have eq568 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq565 eq567
  have eq569 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq568 eq10
  have eq572 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X5) ◇ X5)) ◇ (X2 ◇ (X5 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X5) ◇ X5))))) = X4 := superpose eq568 eq71
  have eq701 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ X2) = X4 := superpose eq568 eq572
  have eq706 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq701 eq569
  have eq710 (X0 X2 : G) : X0 = X2 := superpose eq706 eq706
  have eq712 (X0 : G) : sK0 ≠ X0 := superpose eq710 eq8
  subsumption eq712 eq710


@[equational_result]
theorem Equation18155_implies_Equation2 (G : Type*) [Magma G] (h : Equation18155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X0 ◇ X5))) = X2 := superpose eq12 eq10
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X3) ◇ X4)) = X2 := superpose eq12 eq13
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq26 eq18


@[equational_result]
theorem Equation18157_implies_Equation2 (G : Type*) [Magma G] (h : Equation18157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq11 eq11
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := superpose eq14 eq10
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq24 eq24
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq71 eq56


@[equational_result]
theorem Equation18158_implies_Equation2 (G : Type*) [Magma G] (h : Equation18158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ ((X1 ◇ X4) ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (((X4 ◇ (X2 ◇ X4)) ◇ X0) ◇ X5)) = X3 := superpose eq10 eq11
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq7
  have eq56 (X0 X2 X3 X4 X5 : G) : (X2 ◇ (((X4 ◇ (X2 ◇ X4)) ◇ X0) ◇ X5)) = X3 := superpose eq36 eq28
  have eq62 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq36 eq56
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq62 eq62
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq78 eq63


@[equational_result]
theorem Equation18159_implies_Equation2 (G : Type*) [Magma G] (h : Equation18159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq12 eq18
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq47 eq32


@[equational_result]
theorem Equation18160_implies_Equation2 (G : Type*) [Magma G] (h : Equation18160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation18163_implies_Equation2 (G : Type*) [Magma G] (h : Equation18163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X3 ◇ ((X3 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X2)) = ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ ((X3 ◇ X0) ◇ (X0 ◇ (X3 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) = X0 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X3 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X3))) := superpose eq7 eq9
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X0) = (X0 ◇ (X2 ◇ ((X2 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X0)) ◇ X2))) := superpose eq11 eq9
  have eq26 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq7 eq9
  have eq121 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq7 eq26
  have eq125 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))))) := superpose eq10 eq26
  have eq131 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ (X1 ◇ (X3 ◇ X1)))) ◇ X2)) = (((X3 ◇ X1) ◇ (X1 ◇ (X3 ◇ X1))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X3 ◇ X1) ◇ (X1 ◇ (X3 ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))))) := superpose eq10 eq26
  have eq135 (X0 X1 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq7 eq26
  have eq137 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ X0) := superpose eq7 eq26
  have eq169 (X0 X1 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) = X0 := superpose eq11 eq135
  have eq175 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) := superpose eq11 eq137
  have eq234 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq11 eq175
  have eq239 (X0 X2 X3 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3))) = X0 := superpose eq234 eq21
  have eq279 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = (X0 ◇ X0) := superpose eq234 eq121
  have eq283 (X0 X1 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq234 eq125
  have eq285 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ X2)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))))) := superpose eq234 eq131
  have eq331 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq279 eq11
  have eq337 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X2 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2))) := superpose eq279 eq25
  have eq384 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq169 eq337
  have eq491 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq234 eq283
  have eq492 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose eq239 eq491
  have eq508 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ X2)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose eq492 eq285
  have eq509 (X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ X2)) = (X1 ◇ (X1 ◇ X1)) := superpose eq279 eq508
  have eq643 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq331 eq384
  have eq662 (X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ X2)) = X1 := superpose eq643 eq509
  have eq673 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq662 eq7
  have eq693 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq673 eq384
  have eq754 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq662 eq662
  have eq758 (X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X2))) = X1 := superpose eq754 eq662
  have eq772 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq673 eq758
  have eq776 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq693 eq772
  have eq777 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq693 eq776
  have eq781 (X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = X1 := superpose eq777 eq758
  have eq789 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq693 eq781
  have eq794 (X0 X2 : G) : X0 = X2 := superpose eq789 eq789
  have eq799 (X0 : G) : sK0 ≠ X0 := superpose eq794 eq8
  subsumption eq799 eq794


@[equational_result]
theorem Equation18164_implies_Equation2 (G : Type*) [Magma G] (h : Equation18164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq55 eq23


@[equational_result]
theorem Equation18168_implies_Equation2 (G : Type*) [Magma G] (h : Equation18168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq71 eq23


@[equational_result]
theorem Equation18171_implies_Equation2 (G : Type*) [Magma G] (h : Equation18171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X2 := superpose eq7 eq13
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq16
  have eq41 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq24 eq24
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq41 eq41
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq125 eq70


@[equational_result]
theorem Equation18172_implies_Equation2 (G : Type*) [Magma G] (h : Equation18172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation18174_implies_Equation2 (G : Type*) [Magma G] (h : Equation18174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X1) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq10
  have eq25 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = X4 := superpose eq19 eq12
  have eq38 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq25 eq25
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq25 eq38
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq67 eq39


@[equational_result]
theorem Equation18175_implies_Equation2 (G : Type*) [Magma G] (h : Equation18175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq33 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq18 eq18
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq18 eq33
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq57 eq34


@[equational_result]
theorem Equation18176_implies_Equation2 (G : Type*) [Magma G] (h : Equation18176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ (X4 ◇ ((X4 ◇ X5) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq10
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq46 eq31


@[equational_result]
theorem Equation18177_implies_Equation2 (G : Type*) [Magma G] (h : Equation18177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X7 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq10
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq13 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation18179_implies_Equation2 (G : Type*) [Magma G] (h : Equation18179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X2) = X5 := superpose eq12 eq12
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq37 eq24


@[equational_result]
theorem Equation18180_implies_Equation2 (G : Type*) [Magma G] (h : Equation18180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X2)) = (X0 ◇ (X4 ◇ ((X5 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) ◇ X4))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X0) = (X0 ◇ (X3 ◇ (X2 ◇ X0))) := superpose eq12 eq12
  have eq40 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq12 eq14
  have eq95 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq40
  have eq123 (X0 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ X2) ◇ X4))) = X2 := superpose eq95 eq9
  have eq141 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq95 eq123
  have eq153 (X0 X3 : G) : X0 = X3 := superpose eq141 eq141
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq153 eq8
  subsumption eq172 eq153


@[equational_result]
theorem Equation18181_implies_Equation2 (G : Type*) [Magma G] (h : Equation18181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq55 eq23


@[equational_result]
theorem Equation18182_implies_Equation2 (G : Type*) [Magma G] (h : Equation18182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq55 eq23


@[equational_result]
theorem Equation18184_implies_Equation2 (G : Type*) [Magma G] (h : Equation18184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq12 eq12
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq37 eq24


@[equational_result]
theorem Equation18185_implies_Equation2 (G : Type*) [Magma G] (h : Equation18185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X1) ◇ X2)) = (X0 ◇ (X4 ◇ ((X5 ◇ (X1 ◇ X0)) ◇ X4))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) ◇ (X5 ◇ (X0 ◇ X5))) = X4 := superpose eq7 eq7
  have eq23 (X0 X1 X5 X6 X7 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X5) ◇ (X6 ◇ (X7 ◇ X6))) = X5 := superpose eq7 eq10
  have eq29 (X0 X1 X5 X6 X7 : G) : (((X0 ◇ X1) ◇ X5) ◇ (X6 ◇ (X7 ◇ X6))) = X5 := superpose eq10 eq10
  have eq30 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X3)) = (((X0 ◇ X1) ◇ X2) ◇ (X5 ◇ (X6 ◇ X5))) := superpose eq7 eq10
  have eq46 (X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X2) ◇ X3)) = X2 := superpose eq29 eq30
  have eq47 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq46 eq7
  have eq48 (X0 X1 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ (X1 ◇ X0)) ◇ X4))) = X1 := superpose eq46 eq9
  have eq60 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq46 eq48
  have eq62 (X0 X1 X5 X7 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X5) ◇ X7) = X5 := superpose eq60 eq23
  have eq65 (X0 X5 X7 : G) : ((X0 ◇ X5) ◇ X7) = X5 := superpose eq60 eq62
  have eq66 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq65 eq46
  have eq67 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq66 eq47
  have eq68 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq66 eq60
  have eq98 (X0 X1 : G) : X0 = X1 := superpose eq67 eq68
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq103 eq98


@[equational_result]
theorem Equation18186_implies_Equation2 (G : Type*) [Magma G] (h : Equation18186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq50 eq33


@[equational_result]
theorem Equation18187_implies_Equation2 (G : Type*) [Magma G] (h : Equation18187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq71 eq23


@[equational_result]
theorem Equation18189_implies_Equation2 (G : Type*) [Magma G] (h : Equation18189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X3 ◇ X2)) ◇ X4) ◇ X1) = X4 := superpose eq7 eq12
  have eq49 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq33 eq12
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq49
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq120 eq52


@[equational_result]
theorem Equation18190_implies_Equation2 (G : Type*) [Magma G] (h : Equation18190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X1 ◇ X0) ◇ X0)) = X3 := superpose eq7 eq11
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq12 eq7
  have eq41 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq19 eq19
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq41 eq41
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq126 eq70


@[equational_result]
theorem Equation18191_implies_Equation2 (G : Type*) [Magma G] (h : Equation18191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq11
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq11 eq27
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq74 eq30


@[equational_result]
theorem Equation18192_implies_Equation2 (G : Type*) [Magma G] (h : Equation18192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation18194_implies_Equation2 (G : Type*) [Magma G] (h : Equation18194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X3 := superpose eq7 eq12
  have eq23 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq12 eq13
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq126 eq46


