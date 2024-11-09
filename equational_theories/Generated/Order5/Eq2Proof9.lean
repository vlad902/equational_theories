import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation20077_implies_Equation2 (G : Type*) [Magma G] (h : Equation20077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20079_implies_Equation2 (G : Type*) [Magma G] (h : Equation20079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20080_implies_Equation2 (G : Type*) [Magma G] (h : Equation20080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20081_implies_Equation2 (G : Type*) [Magma G] (h : Equation20081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20082_implies_Equation2 (G : Type*) [Magma G] (h : Equation20082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20084_implies_Equation2 (G : Type*) [Magma G] (h : Equation20084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq83 eq19


@[equational_result]
theorem Equation20085_implies_Equation2 (G : Type*) [Magma G] (h : Equation20085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq58 eq14


@[equational_result]
theorem Equation20086_implies_Equation2 (G : Type*) [Magma G] (h : Equation20086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : ((X1 ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq47 eq14


@[equational_result]
theorem Equation20087_implies_Equation2 (G : Type*) [Magma G] (h : Equation20087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation20089_implies_Equation2 (G : Type*) [Magma G] (h : Equation20089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20090_implies_Equation2 (G : Type*) [Magma G] (h : Equation20090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20091_implies_Equation2 (G : Type*) [Magma G] (h : Equation20091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20092_implies_Equation2 (G : Type*) [Magma G] (h : Equation20092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20094_implies_Equation2 (G : Type*) [Magma G] (h : Equation20094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20095_implies_Equation2 (G : Type*) [Magma G] (h : Equation20095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20096_implies_Equation2 (G : Type*) [Magma G] (h : Equation20096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20097_implies_Equation2 (G : Type*) [Magma G] (h : Equation20097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20099_implies_Equation2 (G : Type*) [Magma G] (h : Equation20099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20100_implies_Equation2 (G : Type*) [Magma G] (h : Equation20100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation20101_implies_Equation2 (G : Type*) [Magma G] (h : Equation20101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20102_implies_Equation2 (G : Type*) [Magma G] (h : Equation20102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20104_implies_Equation2 (G : Type*) [Magma G] (h : Equation20104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20105_implies_Equation2 (G : Type*) [Magma G] (h : Equation20105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20106_implies_Equation2 (G : Type*) [Magma G] (h : Equation20106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20107_implies_Equation2 (G : Type*) [Magma G] (h : Equation20107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20108_implies_Equation2 (G : Type*) [Magma G] (h : Equation20108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20110_implies_Equation2 (G : Type*) [Magma G] (h : Equation20110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq9 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq40 eq34


@[equational_result]
theorem Equation20111_implies_Equation2 (G : Type*) [Magma G] (h : Equation20111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq11
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq7 eq14
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq96 eq27


@[equational_result]
theorem Equation20112_implies_Equation2 (G : Type*) [Magma G] (h : Equation20112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20114_implies_Equation2 (G : Type*) [Magma G] (h : Equation20114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq12
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq27
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq101 eq33


@[equational_result]
theorem Equation20115_implies_Equation2 (G : Type*) [Magma G] (h : Equation20115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X3 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X0) = X2 := superpose eq7 eq7
  have eq27 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X1) := superpose eq7 eq12
  have eq28 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq12
  have eq81 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ (X3 ◇ X4))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = ((X1 ◇ ((X2 ◇ X0) ◇ (((X0 ◇ (X0 ◇ (X3 ◇ X4))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X1))) ◇ X2) := superpose eq9 eq12
  have eq124 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) := superpose eq27 eq10
  have eq137 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1))) = ((((X2 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1))) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq12 eq10
  have eq162 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq28 eq10
  have eq163 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq28 eq10
  have eq165 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0))) = X1 := superpose eq28 eq7
  have eq176 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq137 eq162
  have eq177 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq12 eq176
  have eq178 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq177 eq124
  have eq179 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq177 eq28
  have eq180 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq177 eq178
  have eq187 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq177 eq163
  have eq188 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq177 eq187
  have eq189 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq177 eq188
  have eq191 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0))) = X1 := superpose eq177 eq165
  have eq205 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0)) = X1 := superpose eq179 eq9
  have eq240 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq177 eq10
  have eq251 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X1) := superpose eq177 eq12
  have eq255 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq180 eq240
  have eq260 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0)) = X1 := superpose eq255 eq205
  have eq292 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq260 eq251
  have eq355 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq292 eq177
  have eq356 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X1 := superpose eq292 eq179
  have eq769 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) := superpose eq180 eq7
  have eq786 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq180 eq769
  have eq787 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq255 eq786
  have eq793 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq787 eq189
  have eq794 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) = X1 := superpose eq787 eq191
  have eq845 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq787 eq793
  have eq846 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq355 eq845
  have eq852 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = X1 := superpose eq846 eq794
  have eq853 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq356 eq852
  have eq863 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ (X3 ◇ X4))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = ((X1 ◇ (((X0 ◇ (X0 ◇ (X3 ◇ X4))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X1)) ◇ X2) := superpose eq853 eq81
  have eq1039 (X0 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ (X3 ◇ X4))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = X2 := superpose eq853 eq863
  have eq1040 (X0 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ (X3 ◇ X4))) ◇ X4) = X2 := superpose eq853 eq1039
  have eq1041 (X0 X2 X3 X4 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X4) = X2 := superpose eq853 eq1040
  have eq1042 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X4) = X2 := superpose eq853 eq1041
  have eq1043 (X2 X4 : G) : (X4 ◇ X4) = X2 := superpose eq853 eq1042
  have eq1061 (X0 X2 : G) : X0 = X2 := superpose eq1043 eq1043
  have eq1069 (X0 : G) : sK0 ≠ X0 := superpose eq1061 eq8
  subsumption eq1069 eq1061


@[equational_result]
theorem Equation20116_implies_Equation2 (G : Type*) [Magma G] (h : Equation20116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20119_implies_Equation2 (G : Type*) [Magma G] (h : Equation20119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (((X3 ◇ X2) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) ◇ ((X2 ◇ X0) ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3)))) = X2 := superpose eq9 eq7
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq7 eq10
  have eq32 (X0 X2 X3 : G) : ((X3 ◇ ((((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq7 eq28
  have eq36 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) = ((X3 ◇ ((((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) := superpose eq7 eq28
  have eq71 (X0 X2 X3 : G) : ((X3 ◇ ((((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq7 eq32
  have eq73 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq71 eq36
  have eq75 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) ◇ X0) = X2 := superpose eq73 eq15
  have eq93 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq73 eq75
  have eq137 (X0 X2 : G) : X0 = X2 := superpose eq7 eq93
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq137 eq8
  subsumption eq148 eq137


@[equational_result]
theorem Equation20120_implies_Equation2 (G : Type*) [Magma G] (h : Equation20120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation20122_implies_Equation2 (G : Type*) [Magma G] (h : Equation20122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X4 ◇ X5)) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq142 eq65


@[equational_result]
theorem Equation20123_implies_Equation2 (G : Type*) [Magma G] (h : Equation20123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ X5) ◇ ((X1 ◇ X2) ◇ X5)) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq11
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X4 ◇ (X4 ◇ X5)) ◇ (X2 ◇ X3))) = X4 := superpose eq11 eq7
  have eq34 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq11 eq7
  have eq43 (X0 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ ((X0 ◇ X6) ◇ X5)) = X0 := superpose eq7 eq10
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq43 eq13
  have eq72 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X4 ◇ X5)) ◇ (X2 ◇ X3))) = X4 := superpose eq66 eq30
  have eq88 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq66 eq72
  have eq90 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ (X0 ◇ X1)) = X3 := superpose eq88 eq34
  have eq103 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ X1) = X3 := superpose eq88 eq90
  have eq104 (X0 X1 X3 X4 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X1) = X3 := superpose eq88 eq103
  have eq105 (X1 X3 X4 : G) : ((X3 ◇ X4) ◇ X1) = X3 := superpose eq88 eq104
  have eq106 (X1 X3 X4 : G) : (X4 ◇ X1) = X3 := superpose eq88 eq105
  have eq107 (X0 X3 : G) : X0 = X3 := superpose eq106 eq106
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq112 eq107


@[equational_result]
theorem Equation20124_implies_Equation2 (G : Type*) [Magma G] (h : Equation20124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation20125_implies_Equation2 (G : Type*) [Magma G] (h : Equation20125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20127_implies_Equation2 (G : Type*) [Magma G] (h : Equation20127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq11 eq9
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq40 eq30


@[equational_result]
theorem Equation20129_implies_Equation2 (G : Type*) [Magma G] (h : Equation20129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20131_implies_Equation2 (G : Type*) [Magma G] (h : Equation20131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq27 (X0 X1 : G) : X0 = X1 := superpose eq10 eq9
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq35 eq27


@[equational_result]
theorem Equation20132_implies_Equation2 (G : Type*) [Magma G] (h : Equation20132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1))) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))))) ◇ X2)) = X3 := superpose eq11 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ X2)) = X3 := superpose eq12 eq16
  have eq36 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose eq10 eq11
  have eq82 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3))) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) = X2 := superpose eq10 eq18
  have eq92 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq18
  have eq115 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) = X2 := superpose eq92 eq82
  have eq116 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X1 := superpose eq92 eq36
  have eq118 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq116 eq115
  have eq177 (X0 X2 : G) : X0 = X2 := superpose eq116 eq118
  have eq299 (X0 : G) : sK0 ≠ X0 := superpose eq177 eq8
  subsumption eq299 eq177


@[equational_result]
theorem Equation20133_implies_Equation2 (G : Type*) [Magma G] (h : Equation20133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation20135_implies_Equation2 (G : Type*) [Magma G] (h : Equation20135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq83 eq30


@[equational_result]
theorem Equation20136_implies_Equation2 (G : Type*) [Magma G] (h : Equation20136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq9
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq89 eq35


@[equational_result]
theorem Equation20137_implies_Equation2 (G : Type*) [Magma G] (h : Equation20137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq41 eq15


@[equational_result]
theorem Equation20139_implies_Equation2 (G : Type*) [Magma G] (h : Equation20139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ ((X1 ◇ X2) ◇ X5)) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ X0) = X1 := superpose eq7 eq7
  have eq37 (X0 X1 : G) : X0 = X1 := superpose eq12 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq47 eq37


@[equational_result]
theorem Equation20140_implies_Equation2 (G : Type*) [Magma G] (h : Equation20140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ X3)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X4) = (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4))) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 X5 X6 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ X6) ◇ X4)) = X5 := superpose eq7 eq10
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X5) ◇ ((X1 ◇ X4) ◇ X5)) := superpose eq7 eq11
  have eq67 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = X1 := superpose eq13 eq33
  have eq74 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq67 eq12
  have eq78 (X0 X2 X3 X4 : G) : (X2 ◇ ((X4 ◇ X0) ◇ X3)) = X4 := superpose eq74 eq10
  have eq83 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq74 eq78
  have eq84 (X0 X3 : G) : X0 = X3 := superpose eq83 eq83
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq96 eq84


@[equational_result]
theorem Equation20141_implies_Equation2 (G : Type*) [Magma G] (h : Equation20141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20142_implies_Equation2 (G : Type*) [Magma G] (h : Equation20142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20145_implies_Equation2 (G : Type*) [Magma G] (h : Equation20145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ ((((X0 ◇ (X3 ◇ X0)) ◇ X3) ◇ X0) ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X1) = ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq43 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ X0) := superpose eq7 eq28
  have eq57 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)))) = X2 := superpose eq28 eq9
  have eq105 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq43 eq28
  have eq145 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)))) = X2 := superpose eq105 eq57
  have eq161 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq105 eq145
  have eq280 (X0 X3 : G) : X0 = X3 := superpose eq161 eq161
  have eq468 (X0 : G) : sK0 ≠ X0 := superpose eq280 eq8
  subsumption eq468 eq280


@[equational_result]
theorem Equation20146_implies_Equation2 (G : Type*) [Magma G] (h : Equation20146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq71 eq16


@[equational_result]
theorem Equation20148_implies_Equation2 (G : Type*) [Magma G] (h : Equation20148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq7 eq11
  have eq18 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq46 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq18 eq18
  have eq49 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq18 eq18
  have eq84 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq7 eq10
  have eq101 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq46 eq11
  have eq102 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq46 eq10
  have eq117 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq101 eq46
  have eq118 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq117 eq101
  have eq120 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq118 eq102
  have eq121 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq118 eq120
  have eq122 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq118 eq121
  have eq174 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq84 eq7
  have eq190 (X0 X1 X2 : G) : ((((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq84 eq7
  have eq201 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq174 eq84
  have eq226 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq174 eq190
  have eq247 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq118 eq10
  have eq304 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq18 eq122
  have eq309 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq201 eq122
  have eq330 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq309 eq201
  have eq344 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq330 eq247
  have eq346 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq330 eq344
  have eq347 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq346 eq304
  have eq360 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq347 eq14
  have eq361 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq347 eq18
  have eq365 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq347 eq49
  have eq390 (X0 X1 X2 : G) : ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq360 eq226
  have eq397 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq347 eq365
  have eq398 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq361 eq397
  have eq399 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq118 eq398
  have eq408 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X2 ◇ X1) ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq399 eq390
  have eq491 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq399 eq408
  have eq492 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X1 := superpose eq399 eq491
  have eq493 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq399 eq492
  have eq494 (X0 X1 : G) : X0 = X1 := superpose eq118 eq493
  have eq507 (X0 : G) : sK0 ≠ X0 := superpose eq494 eq8
  subsumption eq507 eq494


@[equational_result]
theorem Equation20150_implies_Equation2 (G : Type*) [Magma G] (h : Equation20150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20153_implies_Equation2 (G : Type*) [Magma G] (h : Equation20153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X2) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2))) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq9
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq7 eq16
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq78 eq55


@[equational_result]
theorem Equation20154_implies_Equation2 (G : Type*) [Magma G] (h : Equation20154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq69 eq16


@[equational_result]
theorem Equation20156_implies_Equation2 (G : Type*) [Magma G] (h : Equation20156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X0) ◇ X1)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq11
  have eq70 (X0 X4 : G) : X0 = X4 := superpose eq7 eq45
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq157 eq70


@[equational_result]
theorem Equation20157_implies_Equation2 (G : Type*) [Magma G] (h : Equation20157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (X2 ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) := superpose eq7 eq7
  have eq40 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq11
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq40
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq146 eq61


@[equational_result]
theorem Equation20158_implies_Equation2 (G : Type*) [Magma G] (h : Equation20158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X3) ◇ X5)) ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq49 (X0 X1 X2 X3 X5 X6 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X5 ◇ X6))) = X3 := superpose eq11 eq9
  have eq50 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X3))) ◇ X2)) = X5 := superpose eq11 eq9
  have eq71 (X0 X2 X4 X5 : G) : (X4 ◇ (X0 ◇ X2)) = X5 := superpose eq49 eq50
  have eq192 (X0 X4 : G) : X0 = X4 := superpose eq7 eq71
  have eq339 (X0 : G) : sK0 ≠ X0 := superpose eq192 eq8
  subsumption eq339 eq192


@[equational_result]
theorem Equation20159_implies_Equation2 (G : Type*) [Magma G] (h : Equation20159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20161_implies_Equation2 (G : Type*) [Magma G] (h : Equation20161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X5 ◇ X4)) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq33 (X0 X5 : G) : X0 = X5 := superpose eq9 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq41 eq33


@[equational_result]
theorem Equation20162_implies_Equation2 (G : Type*) [Magma G] (h : Equation20162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4))) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq7 eq11
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq116 eq42


@[equational_result]
theorem Equation20163_implies_Equation2 (G : Type*) [Magma G] (h : Equation20163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20164_implies_Equation2 (G : Type*) [Magma G] (h : Equation20164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20166_implies_Equation2 (G : Type*) [Magma G] (h : Equation20166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ X2) ◇ X4) ◇ (X5 ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq11
  have eq19 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) = ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X4) ◇ X0) := superpose eq7 eq11
  have eq34 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) = X2 := superpose eq12 eq19
  have eq35 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq34 eq12
  have eq39 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ (X5 ◇ (X1 ◇ X2))) = X0 := superpose eq35 eq13
  have eq49 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X5) = X0 := superpose eq35 eq39
  have eq50 (X0 X1 X5 : G) : (X1 ◇ X5) = X0 := superpose eq35 eq49
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq50 eq50
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq70 eq51


@[equational_result]
theorem Equation20167_implies_Equation2 (G : Type*) [Magma G] (h : Equation20167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq155 eq60


@[equational_result]
theorem Equation20168_implies_Equation2 (G : Type*) [Magma G] (h : Equation20168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20169_implies_Equation2 (G : Type*) [Magma G] (h : Equation20169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation20171_implies_Equation2 (G : Type*) [Magma G] (h : Equation20171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq156 eq61


@[equational_result]
theorem Equation20172_implies_Equation2 (G : Type*) [Magma G] (h : Equation20172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq145 eq56


@[equational_result]
theorem Equation20173_implies_Equation2 (G : Type*) [Magma G] (h : Equation20173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X5 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X3))) ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X4)))) := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11
  have eq50 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (((X1 ◇ (X3 ◇ X4)) ◇ X3) ◇ ((X2 ◇ (X5 ◇ X6)) ◇ X5))))) = X2 := superpose eq9 eq9
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3))))) = X5 := superpose eq11 eq9
  have eq62 (X0 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X3)) = X0 := superpose eq7 eq26
  have eq110 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X2 := superpose eq62 eq50
  have eq127 (X1 X3 X4 X5 : G) : (X4 ◇ (X1 ◇ X3)) = X5 := superpose eq110 eq52
  have eq143 (X0 X4 : G) : X0 = X4 := superpose eq7 eq127
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq143 eq8
  subsumption eq176 eq143


@[equational_result]
theorem Equation20174_implies_Equation2 (G : Type*) [Magma G] (h : Equation20174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation20176_implies_Equation2 (G : Type*) [Magma G] (h : Equation20176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X5 ◇ X5)) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq32
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq112 eq42


@[equational_result]
theorem Equation20177_implies_Equation2 (G : Type*) [Magma G] (h : Equation20177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (X4 ◇ X4))) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) ◇ X0) = X4 := superpose eq7 eq7
  have eq43 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := superpose eq7 eq11
  have eq65 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq43 eq12
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq7 eq65
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq155 eq67


@[equational_result]
theorem Equation20178_implies_Equation2 (G : Type*) [Magma G] (h : Equation20178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ ((X0 ◇ (X4 ◇ X4)) ◇ X4))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq10
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation20179_implies_Equation2 (G : Type*) [Magma G] (h : Equation20179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20181_implies_Equation2 (G : Type*) [Magma G] (h : Equation20181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq35
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq133 eq57


@[equational_result]
theorem Equation20182_implies_Equation2 (G : Type*) [Magma G] (h : Equation20182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq35
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq159 eq57


@[equational_result]
theorem Equation20183_implies_Equation2 (G : Type*) [Magma G] (h : Equation20183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20184_implies_Equation2 (G : Type*) [Magma G] (h : Equation20184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X6 X7 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ ((X0 ◇ (X6 ◇ X7)) ◇ X7))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq10
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation20185_implies_Equation2 (G : Type*) [Magma G] (h : Equation20185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20187_implies_Equation2 (G : Type*) [Magma G] (h : Equation20187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq9 eq9
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq41 eq17


@[equational_result]
theorem Equation20188_implies_Equation2 (G : Type*) [Magma G] (h : Equation20188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq11
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq9 eq7
  have eq42 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq15 eq11
  have eq98 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq32 eq7
  have eq113 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq98 eq14
  have eq120 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq113 eq98
  have eq137 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq113 eq42
  have eq191 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq113 eq120
  have eq225 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose eq113 eq137
  have eq226 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq113 eq225
  have eq227 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq191 eq226
  have eq263 (X0 X2 : G) : X0 = X2 := superpose eq227 eq227
  have eq271 (X0 : G) : sK0 ≠ X0 := superpose eq263 eq8
  subsumption eq271 eq263


@[equational_result]
theorem Equation20189_implies_Equation2 (G : Type*) [Magma G] (h : Equation20189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation20191_implies_Equation2 (G : Type*) [Magma G] (h : Equation20191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) ◇ X0) ◇ (((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)))) = X4 := superpose eq9 eq9
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq9 eq12
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq159 eq50


@[equational_result]
theorem Equation20193_implies_Equation2 (G : Type*) [Magma G] (h : Equation20193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20197_implies_Equation2 (G : Type*) [Magma G] (h : Equation20197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation20199_implies_Equation2 (G : Type*) [Magma G] (h : Equation20199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq163 eq59


@[equational_result]
theorem Equation20200_implies_Equation2 (G : Type*) [Magma G] (h : Equation20200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq88 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq182 eq88


@[equational_result]
theorem Equation20201_implies_Equation2 (G : Type*) [Magma G] (h : Equation20201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20202_implies_Equation2 (G : Type*) [Magma G] (h : Equation20202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20204_implies_Equation2 (G : Type*) [Magma G] (h : Equation20204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq9 eq9
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq107 eq35


@[equational_result]
theorem Equation20205_implies_Equation2 (G : Type*) [Magma G] (h : Equation20205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (((X1 ◇ X2) ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) = X0 := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)))) := superpose eq7 eq11
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ (X0 ◇ X1)) = X2 := superpose eq11 eq7
  have eq69 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X0)))) ◇ X3) = (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X1)) ◇ ((X2 ◇ X3) ◇ X0)))) := superpose eq9 eq9
  have eq99 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = ((X2 ◇ (X2 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X0)))) ◇ X3) := superpose eq16 eq69
  have eq138 (X0 X1 X2 : G) : ((((X0 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X1 := superpose eq11 eq13
  have eq187 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) = X0 := superpose eq7 eq10
  have eq243 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq16 eq187
  have eq308 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1))) ◇ X0) = X0 := superpose eq15 eq12
  have eq311 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq15 eq11
  have eq380 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) := superpose eq243 eq10
  have eq382 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq243 eq9
  have eq403 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq243 eq382
  have eq404 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq7 eq403
  have eq435 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq9 eq20
  have eq489 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X1 := superpose eq404 eq7
  have eq491 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) = X3 := superpose eq404 eq9
  have eq494 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq404 eq11
  have eq507 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq404 eq12
  have eq561 (X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2))) = X3 := superpose eq507 eq491
  have eq562 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X1 := superpose eq507 eq489
  have eq573 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq562 eq243
  have eq578 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq573 eq380
  have eq587 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) := superpose eq573 eq494
  have eq598 (X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)))) = X3 := superpose eq578 eq561
  have eq607 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq587 eq435
  have eq608 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq607 eq578
  have eq892 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq573 eq608
  have eq893 (X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X3)) = X3 := superpose eq892 eq598
  have eq895 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = ((X2 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) := superpose eq893 eq99
  have eq905 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X2 ◇ X3) ◇ X0) := superpose eq893 eq895
  have eq911 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X1 := superpose eq905 eq138
  have eq915 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq905 eq308
  have eq916 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq905 eq311
  have eq933 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq562 eq911
  have eq948 (X0 X1 X2 : G) : ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := superpose eq905 eq915
  have eq949 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq905 eq948
  have eq950 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq933 eq916
  have eq951 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq949 eq950
  have eq952 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq951 eq905
  have eq1002 (X0 X1 : G) : X0 = X1 := superpose eq952 eq951
  have eq1006 (X0 : G) : sK0 ≠ X0 := superpose eq1002 eq8
  subsumption eq1006 eq1002


@[equational_result]
theorem Equation20206_implies_Equation2 (G : Type*) [Magma G] (h : Equation20206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq64 eq16


@[equational_result]
theorem Equation20208_implies_Equation2 (G : Type*) [Magma G] (h : Equation20208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20209_implies_Equation2 (G : Type*) [Magma G] (h : Equation20209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20210_implies_Equation2 (G : Type*) [Magma G] (h : Equation20210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20212_implies_Equation2 (G : Type*) [Magma G] (h : Equation20212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation20213_implies_Equation2 (G : Type*) [Magma G] (h : Equation20213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation20214_implies_Equation2 (G : Type*) [Magma G] (h : Equation20214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20216_implies_Equation2 (G : Type*) [Magma G] (h : Equation20216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20217_implies_Equation2 (G : Type*) [Magma G] (h : Equation20217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20218_implies_Equation2 (G : Type*) [Magma G] (h : Equation20218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20219_implies_Equation2 (G : Type*) [Magma G] (h : Equation20219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20223_implies_Equation2 (G : Type*) [Magma G] (h : Equation20223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq70 eq16


@[equational_result]
theorem Equation20225_implies_Equation2 (G : Type*) [Magma G] (h : Equation20225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20226_implies_Equation2 (G : Type*) [Magma G] (h : Equation20226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20227_implies_Equation2 (G : Type*) [Magma G] (h : Equation20227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20229_implies_Equation2 (G : Type*) [Magma G] (h : Equation20229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20230_implies_Equation2 (G : Type*) [Magma G] (h : Equation20230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20231_implies_Equation2 (G : Type*) [Magma G] (h : Equation20231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20233_implies_Equation2 (G : Type*) [Magma G] (h : Equation20233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20234_implies_Equation2 (G : Type*) [Magma G] (h : Equation20234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20235_implies_Equation2 (G : Type*) [Magma G] (h : Equation20235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20236_implies_Equation2 (G : Type*) [Magma G] (h : Equation20236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20238_implies_Equation2 (G : Type*) [Magma G] (h : Equation20238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq42 eq18


@[equational_result]
theorem Equation20239_implies_Equation2 (G : Type*) [Magma G] (h : Equation20239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq36 eq19


@[equational_result]
theorem Equation20240_implies_Equation2 (G : Type*) [Magma G] (h : Equation20240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20241_implies_Equation2 (G : Type*) [Magma G] (h : Equation20241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation20243_implies_Equation2 (G : Type*) [Magma G] (h : Equation20243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20244_implies_Equation2 (G : Type*) [Magma G] (h : Equation20244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20245_implies_Equation2 (G : Type*) [Magma G] (h : Equation20245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20246_implies_Equation2 (G : Type*) [Magma G] (h : Equation20246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20248_implies_Equation2 (G : Type*) [Magma G] (h : Equation20248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20249_implies_Equation2 (G : Type*) [Magma G] (h : Equation20249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20250_implies_Equation2 (G : Type*) [Magma G] (h : Equation20250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20251_implies_Equation2 (G : Type*) [Magma G] (h : Equation20251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20253_implies_Equation2 (G : Type*) [Magma G] (h : Equation20253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20254_implies_Equation2 (G : Type*) [Magma G] (h : Equation20254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20255_implies_Equation2 (G : Type*) [Magma G] (h : Equation20255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20256_implies_Equation2 (G : Type*) [Magma G] (h : Equation20256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20258_implies_Equation2 (G : Type*) [Magma G] (h : Equation20258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20259_implies_Equation2 (G : Type*) [Magma G] (h : Equation20259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20260_implies_Equation2 (G : Type*) [Magma G] (h : Equation20260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20261_implies_Equation2 (G : Type*) [Magma G] (h : Equation20261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20262_implies_Equation2 (G : Type*) [Magma G] (h : Equation20262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20265_implies_Equation2 (G : Type*) [Magma G] (h : Equation20265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq47 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq11
  have eq60 (X0 X2 : G) : X0 = X2 := superpose eq7 eq47
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq122 eq60


@[equational_result]
theorem Equation20266_implies_Equation2 (G : Type*) [Magma G] (h : Equation20266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq72 eq16


@[equational_result]
theorem Equation20270_implies_Equation2 (G : Type*) [Magma G] (h : Equation20270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation20273_implies_Equation2 (G : Type*) [Magma G] (h : Equation20273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) ◇ ((((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ ((((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2))) ◇ ((((((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) ◇ X0) ◇ ((((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)))) = X3 := superpose eq9 eq7
  have eq41 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ ((((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X3) ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))))) = X4 := superpose eq10 eq9
  have eq47 (X2 X4 : G) : (X2 ◇ X2) = X4 := superpose eq15 eq41
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq7 eq47
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq138 eq48


@[equational_result]
theorem Equation20274_implies_Equation2 (G : Type*) [Magma G] (h : Equation20274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq72 eq16


@[equational_result]
theorem Equation20276_implies_Equation2 (G : Type*) [Magma G] (h : Equation20276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq88 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq183 eq88


@[equational_result]
theorem Equation20277_implies_Equation2 (G : Type*) [Magma G] (h : Equation20277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq80 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq174 eq80


@[equational_result]
theorem Equation20278_implies_Equation2 (G : Type*) [Magma G] (h : Equation20278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((((X2 ◇ (X0 ◇ X3)) ◇ X3) ◇ (X4 ◇ X5)) ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) := superpose eq7 eq7
  have eq16 (X0 X1 X5 X6 : G) : (X1 ◇ X0) = ((X5 ◇ (X6 ◇ X1)) ◇ X0) := superpose eq7 eq11
  have eq26 (X0 X3 X4 X5 : G) : (X0 ◇ (((X3 ◇ X3) ◇ (X4 ◇ X5)) ◇ X5)) = X4 := superpose eq16 eq9
  have eq28 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X5)) = X4 := superpose eq16 eq26
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq48 eq38


@[equational_result]
theorem Equation20279_implies_Equation2 (G : Type*) [Magma G] (h : Equation20279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation20283_implies_Equation2 (G : Type*) [Magma G] (h : Equation20283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq70 eq16


@[equational_result]
theorem Equation20285_implies_Equation2 (G : Type*) [Magma G] (h : Equation20285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20286_implies_Equation2 (G : Type*) [Magma G] (h : Equation20286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20287_implies_Equation2 (G : Type*) [Magma G] (h : Equation20287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20289_implies_Equation2 (G : Type*) [Magma G] (h : Equation20289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation20290_implies_Equation2 (G : Type*) [Magma G] (h : Equation20290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation20291_implies_Equation2 (G : Type*) [Magma G] (h : Equation20291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20293_implies_Equation2 (G : Type*) [Magma G] (h : Equation20293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20294_implies_Equation2 (G : Type*) [Magma G] (h : Equation20294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20295_implies_Equation2 (G : Type*) [Magma G] (h : Equation20295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20296_implies_Equation2 (G : Type*) [Magma G] (h : Equation20296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20299_implies_Equation2 (G : Type*) [Magma G] (h : Equation20299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ (((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X1) = ((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X1) = X0 := superpose eq7 eq10
  have eq44 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X1) = X3 := superpose eq19 eq19
  have eq60 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X1))) = X1 := superpose eq44 eq13
  have eq66 (X0 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = X3 := superpose eq60 eq10
  have eq68 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq66 eq7
  have eq83 (X0 X3 : G) : X0 = X3 := superpose eq68 eq68
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq92 eq83


@[equational_result]
theorem Equation20300_implies_Equation2 (G : Type*) [Magma G] (h : Equation20300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq81 eq15


@[equational_result]
theorem Equation20302_implies_Equation2 (G : Type*) [Magma G] (h : Equation20302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20303_implies_Equation2 (G : Type*) [Magma G] (h : Equation20303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20304_implies_Equation2 (G : Type*) [Magma G] (h : Equation20304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20306_implies_Equation2 (G : Type*) [Magma G] (h : Equation20306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20307_implies_Equation2 (G : Type*) [Magma G] (h : Equation20307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20308_implies_Equation2 (G : Type*) [Magma G] (h : Equation20308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20310_implies_Equation2 (G : Type*) [Magma G] (h : Equation20310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20311_implies_Equation2 (G : Type*) [Magma G] (h : Equation20311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20312_implies_Equation2 (G : Type*) [Magma G] (h : Equation20312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20313_implies_Equation2 (G : Type*) [Magma G] (h : Equation20313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20315_implies_Equation2 (G : Type*) [Magma G] (h : Equation20315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation20316_implies_Equation2 (G : Type*) [Magma G] (h : Equation20316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X3))) = X3 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq71 eq19


@[equational_result]
theorem Equation20317_implies_Equation2 (G : Type*) [Magma G] (h : Equation20317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X5 ◇ X0)) := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) = X4 := superpose eq11 eq11
  have eq28 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = X4 := superpose eq21 eq18
  have eq34 (X0 X1 X3 X4 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0)))) = X4 := superpose eq28 eq11
  have eq43 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq28 eq34
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq46 eq44


@[equational_result]
theorem Equation20318_implies_Equation2 (G : Type*) [Magma G] (h : Equation20318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation20320_implies_Equation2 (G : Type*) [Magma G] (h : Equation20320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20321_implies_Equation2 (G : Type*) [Magma G] (h : Equation20321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20322_implies_Equation2 (G : Type*) [Magma G] (h : Equation20322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20323_implies_Equation2 (G : Type*) [Magma G] (h : Equation20323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20325_implies_Equation2 (G : Type*) [Magma G] (h : Equation20325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20326_implies_Equation2 (G : Type*) [Magma G] (h : Equation20326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20327_implies_Equation2 (G : Type*) [Magma G] (h : Equation20327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20328_implies_Equation2 (G : Type*) [Magma G] (h : Equation20328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20330_implies_Equation2 (G : Type*) [Magma G] (h : Equation20330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20331_implies_Equation2 (G : Type*) [Magma G] (h : Equation20331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20332_implies_Equation2 (G : Type*) [Magma G] (h : Equation20332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20333_implies_Equation2 (G : Type*) [Magma G] (h : Equation20333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20335_implies_Equation2 (G : Type*) [Magma G] (h : Equation20335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20336_implies_Equation2 (G : Type*) [Magma G] (h : Equation20336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20337_implies_Equation2 (G : Type*) [Magma G] (h : Equation20337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20338_implies_Equation2 (G : Type*) [Magma G] (h : Equation20338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20339_implies_Equation2 (G : Type*) [Magma G] (h : Equation20339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20341_implies_Equation2 (G : Type*) [Magma G] (h : Equation20341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X5 ◇ X5)) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq165 eq65


@[equational_result]
theorem Equation20342_implies_Equation2 (G : Type*) [Magma G] (h : Equation20342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq52 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq12
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq7 eq52
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq153 eq68


@[equational_result]
theorem Equation20343_implies_Equation2 (G : Type*) [Magma G] (h : Equation20343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation20344_implies_Equation2 (G : Type*) [Magma G] (h : Equation20344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20346_implies_Equation2 (G : Type*) [Magma G] (h : Equation20346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq76 eq57


@[equational_result]
theorem Equation20347_implies_Equation2 (G : Type*) [Magma G] (h : Equation20347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X5 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ X3)) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) = X0 := superpose eq7 eq11
  have eq38 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq25 eq9
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq38 eq38
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation20348_implies_Equation2 (G : Type*) [Magma G] (h : Equation20348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X5 ◇ (X1 ◇ X2))) ◇ X4)) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq9 eq9
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq155 eq44


@[equational_result]
theorem Equation20349_implies_Equation2 (G : Type*) [Magma G] (h : Equation20349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20351_implies_Equation2 (G : Type*) [Magma G] (h : Equation20351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X3) = ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) ◇ ((X5 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ X3)) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) = X0 := superpose eq7 eq11
  have eq38 (X0 X1 X3 X4 X5 : G) : (X4 ◇ X3) = (X0 ◇ ((X5 ◇ X0) ◇ X1)) := superpose eq25 eq10
  have eq55 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq38
  have eq80 (X0 X4 : G) : X0 = X4 := superpose eq7 eq55
  have eq181 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq181 eq80


@[equational_result]
theorem Equation20352_implies_Equation2 (G : Type*) [Magma G] (h : Equation20352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X5 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X4 : G) : (X4 ◇ (X0 ◇ X2)) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = X0 := superpose eq7 eq11
  have eq34 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq21 eq9
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq34
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq60 eq38


@[equational_result]
theorem Equation20353_implies_Equation2 (G : Type*) [Magma G] (h : Equation20353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation20354_implies_Equation2 (G : Type*) [Magma G] (h : Equation20354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation20356_implies_Equation2 (G : Type*) [Magma G] (h : Equation20356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X5 ◇ X4)) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq37 (X0 X7 : G) : X0 = X7 := superpose eq9 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq57 eq37


@[equational_result]
theorem Equation20357_implies_Equation2 (G : Type*) [Magma G] (h : Equation20357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4))) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq11
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq150 eq42


@[equational_result]
theorem Equation20358_implies_Equation2 (G : Type*) [Magma G] (h : Equation20358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation20359_implies_Equation2 (G : Type*) [Magma G] (h : Equation20359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20361_implies_Equation2 (G : Type*) [Magma G] (h : Equation20361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 X6 X7 : G) : (X0 ◇ ((X5 ◇ (X6 ◇ X7)) ◇ (X1 ◇ X2))) = X6 := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq65 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq173 eq65


@[equational_result]
theorem Equation20362_implies_Equation2 (G : Type*) [Magma G] (h : Equation20362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X5) = ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq83 (X0 X5 : G) : X0 = X5 := superpose eq7 eq25
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq177 eq83


@[equational_result]
theorem Equation20363_implies_Equation2 (G : Type*) [Magma G] (h : Equation20363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20364_implies_Equation2 (G : Type*) [Magma G] (h : Equation20364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation20365_implies_Equation2 (G : Type*) [Magma G] (h : Equation20365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20367_implies_Equation2 (G : Type*) [Magma G] (h : Equation20367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq63 eq25


@[equational_result]
theorem Equation20368_implies_Equation2 (G : Type*) [Magma G] (h : Equation20368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X0 ◇ X3)) = X4 := superpose eq7 eq7
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq62 eq25


@[equational_result]
theorem Equation20369_implies_Equation2 (G : Type*) [Magma G] (h : Equation20369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ ((X1 ◇ X2) ◇ X5)) ◇ X4)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X0 ◇ (X2 ◇ X4))) = X1 := superpose eq7 eq7
  have eq38 (X0 X1 : G) : X0 = X1 := superpose eq9 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq48 eq38


@[equational_result]
theorem Equation20370_implies_Equation2 (G : Type*) [Magma G] (h : Equation20370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation20372_implies_Equation2 (G : Type*) [Magma G] (h : Equation20372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20373_implies_Equation2 (G : Type*) [Magma G] (h : Equation20373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20374_implies_Equation2 (G : Type*) [Magma G] (h : Equation20374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20375_implies_Equation2 (G : Type*) [Magma G] (h : Equation20375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20377_implies_Equation2 (G : Type*) [Magma G] (h : Equation20377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20378_implies_Equation2 (G : Type*) [Magma G] (h : Equation20378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20379_implies_Equation2 (G : Type*) [Magma G] (h : Equation20379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20380_implies_Equation2 (G : Type*) [Magma G] (h : Equation20380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20382_implies_Equation2 (G : Type*) [Magma G] (h : Equation20382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20383_implies_Equation2 (G : Type*) [Magma G] (h : Equation20383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20384_implies_Equation2 (G : Type*) [Magma G] (h : Equation20384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20385_implies_Equation2 (G : Type*) [Magma G] (h : Equation20385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20387_implies_Equation2 (G : Type*) [Magma G] (h : Equation20387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20388_implies_Equation2 (G : Type*) [Magma G] (h : Equation20388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20389_implies_Equation2 (G : Type*) [Magma G] (h : Equation20389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20390_implies_Equation2 (G : Type*) [Magma G] (h : Equation20390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20391_implies_Equation2 (G : Type*) [Magma G] (h : Equation20391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20393_implies_Equation2 (G : Type*) [Magma G] (h : Equation20393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq63 eq25


@[equational_result]
theorem Equation20394_implies_Equation2 (G : Type*) [Magma G] (h : Equation20394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X3 ◇ X0)) ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 X4 : G) : (X4 ◇ (X3 ◇ X0)) = ((X1 ◇ X0) ◇ (X3 ◇ X0)) := superpose eq7 eq11
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2)))) = X4 := superpose eq10 eq7
  have eq53 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X6 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ ((X4 ◇ X5) ◇ (X1 ◇ (X2 ◇ X3))))) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ ((X4 ◇ X5) ◇ (X1 ◇ (X2 ◇ X3)))))) = X2 := superpose eq10 eq11
  have eq84 (X0 X1 X2 X3 X4 X5 X7 : G) : (X5 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2)))) = ((X7 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2)))) := superpose eq10 eq16
  have eq124 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2)))) = X4 := superpose eq49 eq84
  have eq127 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X6 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ ((X4 ◇ X5) ◇ (X1 ◇ (X2 ◇ X3))))) ◇ X5) = X2 := superpose eq124 eq53
  have eq129 (X2 X5 : G) : (X5 ◇ X5) = X2 := superpose eq124 eq127
  have eq156 (X0 X3 : G) : X0 = X3 := superpose eq7 eq129
  have eq204 (X0 : G) : sK0 ≠ X0 := superpose eq156 eq8
  subsumption eq204 eq156


@[equational_result]
theorem Equation20395_implies_Equation2 (G : Type*) [Magma G] (h : Equation20395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation20396_implies_Equation2 (G : Type*) [Magma G] (h : Equation20396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq66 eq16


@[equational_result]
theorem Equation20398_implies_Equation2 (G : Type*) [Magma G] (h : Equation20398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20399_implies_Equation2 (G : Type*) [Magma G] (h : Equation20399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20400_implies_Equation2 (G : Type*) [Magma G] (h : Equation20400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20401_implies_Equation2 (G : Type*) [Magma G] (h : Equation20401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20403_implies_Equation2 (G : Type*) [Magma G] (h : Equation20403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20404_implies_Equation2 (G : Type*) [Magma G] (h : Equation20404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20405_implies_Equation2 (G : Type*) [Magma G] (h : Equation20405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20406_implies_Equation2 (G : Type*) [Magma G] (h : Equation20406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20408_implies_Equation2 (G : Type*) [Magma G] (h : Equation20408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20409_implies_Equation2 (G : Type*) [Magma G] (h : Equation20409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20410_implies_Equation2 (G : Type*) [Magma G] (h : Equation20410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20411_implies_Equation2 (G : Type*) [Magma G] (h : Equation20411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20413_implies_Equation2 (G : Type*) [Magma G] (h : Equation20413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20414_implies_Equation2 (G : Type*) [Magma G] (h : Equation20414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20415_implies_Equation2 (G : Type*) [Magma G] (h : Equation20415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20416_implies_Equation2 (G : Type*) [Magma G] (h : Equation20416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20417_implies_Equation2 (G : Type*) [Magma G] (h : Equation20417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20419_implies_Equation2 (G : Type*) [Magma G] (h : Equation20419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation20420_implies_Equation2 (G : Type*) [Magma G] (h : Equation20420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X5)) = X3 := superpose eq11 eq7
  have eq32 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) = X2 := superpose eq11 eq7
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X5) = ((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq11 eq7
  have eq35 (X1 X5 : G) : (X1 ◇ X5) = X1 := superpose eq32 eq33
  have eq36 (X0 X1 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ X5)) = X3 := superpose eq35 eq27
  have eq57 (X0 X1 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X0 ◇ X1)) = X3 := superpose eq35 eq36
  have eq58 (X0 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X0) = X3 := superpose eq35 eq57
  have eq59 (X0 X3 X4 : G) : (X4 ◇ X0) = X3 := superpose eq35 eq58
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq59 eq59
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq79 eq60


@[equational_result]
theorem Equation20421_implies_Equation2 (G : Type*) [Magma G] (h : Equation20421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20422_implies_Equation2 (G : Type*) [Magma G] (h : Equation20422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation20424_implies_Equation2 (G : Type*) [Magma G] (h : Equation20424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20425_implies_Equation2 (G : Type*) [Magma G] (h : Equation20425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20426_implies_Equation2 (G : Type*) [Magma G] (h : Equation20426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20427_implies_Equation2 (G : Type*) [Magma G] (h : Equation20427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20429_implies_Equation2 (G : Type*) [Magma G] (h : Equation20429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20430_implies_Equation2 (G : Type*) [Magma G] (h : Equation20430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20431_implies_Equation2 (G : Type*) [Magma G] (h : Equation20431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20432_implies_Equation2 (G : Type*) [Magma G] (h : Equation20432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20434_implies_Equation2 (G : Type*) [Magma G] (h : Equation20434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20435_implies_Equation2 (G : Type*) [Magma G] (h : Equation20435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20436_implies_Equation2 (G : Type*) [Magma G] (h : Equation20436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20437_implies_Equation2 (G : Type*) [Magma G] (h : Equation20437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20439_implies_Equation2 (G : Type*) [Magma G] (h : Equation20439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20440_implies_Equation2 (G : Type*) [Magma G] (h : Equation20440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20441_implies_Equation2 (G : Type*) [Magma G] (h : Equation20441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20442_implies_Equation2 (G : Type*) [Magma G] (h : Equation20442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20443_implies_Equation2 (G : Type*) [Magma G] (h : Equation20443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20445_implies_Equation2 (G : Type*) [Magma G] (h : Equation20445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation20446_implies_Equation2 (G : Type*) [Magma G] (h : Equation20446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation20447_implies_Equation2 (G : Type*) [Magma G] (h : Equation20447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ X0) = X6 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20448_implies_Equation2 (G : Type*) [Magma G] (h : Equation20448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ X0) = X6 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20449_implies_Equation2 (G : Type*) [Magma G] (h : Equation20449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation20451_implies_Equation2 (G : Type*) [Magma G] (h : Equation20451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20452_implies_Equation2 (G : Type*) [Magma G] (h : Equation20452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20453_implies_Equation2 (G : Type*) [Magma G] (h : Equation20453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20454_implies_Equation2 (G : Type*) [Magma G] (h : Equation20454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20455_implies_Equation2 (G : Type*) [Magma G] (h : Equation20455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20457_implies_Equation2 (G : Type*) [Magma G] (h : Equation20457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20458_implies_Equation2 (G : Type*) [Magma G] (h : Equation20458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20459_implies_Equation2 (G : Type*) [Magma G] (h : Equation20459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20460_implies_Equation2 (G : Type*) [Magma G] (h : Equation20460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20461_implies_Equation2 (G : Type*) [Magma G] (h : Equation20461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20463_implies_Equation2 (G : Type*) [Magma G] (h : Equation20463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20464_implies_Equation2 (G : Type*) [Magma G] (h : Equation20464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20465_implies_Equation2 (G : Type*) [Magma G] (h : Equation20465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20466_implies_Equation2 (G : Type*) [Magma G] (h : Equation20466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20467_implies_Equation2 (G : Type*) [Magma G] (h : Equation20467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20469_implies_Equation2 (G : Type*) [Magma G] (h : Equation20469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20470_implies_Equation2 (G : Type*) [Magma G] (h : Equation20470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20471_implies_Equation2 (G : Type*) [Magma G] (h : Equation20471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20472_implies_Equation2 (G : Type*) [Magma G] (h : Equation20472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20473_implies_Equation2 (G : Type*) [Magma G] (h : Equation20473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20475_implies_Equation2 (G : Type*) [Magma G] (h : Equation20475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20476_implies_Equation2 (G : Type*) [Magma G] (h : Equation20476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20477_implies_Equation2 (G : Type*) [Magma G] (h : Equation20477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20478_implies_Equation2 (G : Type*) [Magma G] (h : Equation20478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20479_implies_Equation2 (G : Type*) [Magma G] (h : Equation20479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20480_implies_Equation2 (G : Type*) [Magma G] (h : Equation20480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20686_implies_Equation2 (G : Type*) [Magma G] (h : Equation20686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq7
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq14
  have eq21 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq11 eq14
  have eq23 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq14 eq11
  have eq24 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq19 eq23
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq24 eq21
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq24 eq25
  have eq31 (X0 X1 : G) : X0 = X1 := superpose eq16 eq30
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq39 eq31


@[equational_result]
theorem Equation20689_implies_Equation2 (G : Type*) [Magma G] (h : Equation20689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq10
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq12
  have eq21 (X0 X1 : G) : X0 = X1 := superpose eq11 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq24 eq21


@[equational_result]
theorem Equation20691_implies_Equation2 (G : Type*) [Magma G] (h : Equation20691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X1) = (X0 ◇ ((((((X0 ◇ X0) ◇ X2) ◇ X1) ◇ (((X0 ◇ X0) ◇ X2) ◇ X1)) ◇ X3) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) = X1 := superpose eq10 eq7
  have eq50 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq10 eq9
  have eq71 (X0 X1 X2 X4 : G) : (((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) ◇ (X4 ◇ X4)) ◇ X4) ◇ X0) = X4 := superpose eq9 eq11
  have eq72 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) ◇ X3)) = X0 := superpose eq9 eq7
  have eq78 (X0 X1 X2 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ X4)) ◇ X4) ◇ X0) = X4 := superpose eq10 eq71
  have eq79 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := superpose eq10 eq72
  have eq130 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq17 eq79
  have eq172 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq130 eq50
  have eq201 (X0 X4 : G) : (((X0 ◇ (X4 ◇ X4)) ◇ X4) ◇ X0) = X4 := superpose eq172 eq78
  have eq212 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq172 eq201
  have eq235 (X0 X1 : G) : X0 = X1 := superpose eq10 eq212
  have eq255 (X0 : G) : sK0 ≠ X0 := superpose eq235 eq8
  subsumption eq255 eq235


@[equational_result]
theorem Equation20692_implies_Equation2 (G : Type*) [Magma G] (h : Equation20692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ ((((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) = X0 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X1 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X2) ◇ X2)) := superpose eq7 eq10
  have eq21 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq7 eq10
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X1 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X2) ◇ X2))) := superpose eq10 eq11
  have eq32 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X1)) := superpose eq7 eq21
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) = ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq7 eq21
  have eq41 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq21 eq7
  have eq44 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((X2 ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq21 eq10
  have eq54 (X0 X1 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq35
  have eq62 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) = X0 := superpose eq54 eq44
  have eq87 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) ◇ (((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1)) ◇ X3) ◇ X3))) = X0 := superpose eq9 eq7
  have eq98 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X3) ◇ X3)))) := superpose eq7 eq41
  have eq117 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq11 eq98
  have eq171 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq117
  have eq189 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq171 eq10
  have eq191 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) := superpose eq171 eq19
  have eq193 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq171 eq21
  have eq197 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) := superpose eq171 eq30
  have eq198 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq171 eq32
  have eq236 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3) ◇ X3))) = X0 := superpose eq171 eq87
  have eq240 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X2)) := superpose eq171 eq191
  have eq246 (X0 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq193 eq41
  have eq248 (X0 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq193 eq62
  have eq259 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) := superpose eq171 eq197
  have eq260 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq193 eq198
  have eq261 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq246 eq260
  have eq262 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq261 eq259
  have eq264 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq261 eq240
  have eq286 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X3))) = X0 := superpose eq171 eq236
  have eq317 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq264 eq193
  have eq328 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq262 eq317
  have eq372 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq189 eq328
  have eq389 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq246 eq372
  have eq390 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq389 eq248
  have eq399 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq390 eq171
  have eq401 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := superpose eq399 eq286
  have eq417 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq399 eq389
  have eq421 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X1 ◇ X3)) = X0 := superpose eq399 eq401
  have eq422 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq399 eq421
  have eq423 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq399 eq422
  have eq446 (X0 X1 : G) : X0 = X1 := superpose eq423 eq417
  have eq465 (X0 : G) : sK0 ≠ X0 := superpose eq446 eq8
  subsumption eq465 eq446


@[equational_result]
theorem Equation20693_implies_Equation2 (G : Type*) [Magma G] (h : Equation20693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20696_implies_Equation2 (G : Type*) [Magma G] (h : Equation20696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq13 eq14
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq11 eq10
  have eq36 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq18 eq22
  have eq37 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq13 eq36
  have eq69 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq18
  have eq73 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq69
  have eq74 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq73 eq37
  have eq81 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq73 eq74
  have eq85 (X0 X1 : G) : X0 = X1 := superpose eq81 eq73
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq87 eq85


@[equational_result]
theorem Equation20699_implies_Equation2 (G : Type*) [Magma G] (h : Equation20699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = X1 := superpose eq13 eq12
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq18 eq10
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq19 eq11
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq13 eq30
  have eq32 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq31 eq18
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq32 eq11
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation20701_implies_Equation2 (G : Type*) [Magma G] (h : Equation20701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ X1) := superpose eq11 eq11
  have eq14 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = (X1 ◇ X1) := superpose eq13 eq12
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X1))) := superpose eq18 eq10
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq11 eq19
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq26
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq11 eq37
  have eq72 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq43 eq14
  have eq80 (X0 X1 : G) : X0 = X1 := superpose eq11 eq72
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq93 eq80


@[equational_result]
theorem Equation20703_implies_Equation2 (G : Type*) [Magma G] (h : Equation20703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20705_implies_Equation2 (G : Type*) [Magma G] (h : Equation20705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq23 (X0 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := superpose eq11 eq10
  have eq36 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq23 eq23
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq23 eq7
  have eq76 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq36 eq7
  have eq83 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq36 eq23
  have eq85 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq83
  have eq91 (X0 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq85 eq23
  have eq94 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq85 eq38
  have eq101 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq85 eq76
  have eq106 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq85 eq101
  have eq107 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X0 := superpose eq85 eq106
  have eq150 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq85 eq7
  have eq213 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq94
  have eq284 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq107 eq10
  have eq310 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq85 eq284
  have eq311 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq85 eq310
  have eq313 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq311 eq150
  have eq318 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq313 eq213
  have eq321 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq313 eq318
  have eq597 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq321 eq91
  have eq599 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq321 eq597
  have eq600 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = X0 := superpose eq599 eq91
  have eq604 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq599 eq600
  have eq605 (X0 X1 : G) : X0 = X1 := superpose eq604 eq599
  have eq607 (X0 : G) : sK0 ≠ X0 := superpose eq605 eq8
  subsumption eq607 eq605


@[equational_result]
theorem Equation20706_implies_Equation2 (G : Type*) [Magma G] (h : Equation20706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = (X0 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) := superpose eq7 eq12
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq18 (X0 X2 : G) : (X0 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) = X0 := superpose eq12 eq7
  have eq21 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq18 eq13
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq21 eq21
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq21 eq12
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq33 eq30
  have eq39 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq35
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq33 eq39
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation20707_implies_Equation2 (G : Type*) [Magma G] (h : Equation20707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq12 eq7
  have eq26 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq12 eq10
  have eq32 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X3) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq10 eq12
  have eq34 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq26 eq32
  have eq42 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq12 eq15
  have eq49 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq12
  have eq51 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq42 eq49
  have eq57 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq51 eq34
  have eq63 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq51 eq57
  have eq64 (X0 X1 : G) : X0 = X1 := superpose eq14 eq63
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq72 eq64


@[equational_result]
theorem Equation20709_implies_Equation2 (G : Type*) [Magma G] (h : Equation20709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X1) = (X0 ◇ ((((((X0 ◇ X2) ◇ X1) ◇ X1) ◇ X3) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (((((X0 ◇ X2) ◇ X1) ◇ X1) ◇ X3) ◇ X3)) = X0 := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (X0 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) := superpose eq7 eq10
  have eq18 (X0 X1 : G) : (X1 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq10 eq7
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = (((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq12 eq11
  have eq57 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3) ◇ X3) = (X0 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) := superpose eq12 eq10
  have eq73 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ ((((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq10 eq9
  have eq104 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ X1) ◇ ((((X2 ◇ X3) ◇ X3) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq10 eq13
  have eq105 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) = ((X0 ◇ X1) ◇ ((((X3 ◇ X4) ◇ X4) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq13 eq13
  have eq136 (X0 X1 : G) : ((((((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq13 eq11
  have eq147 (X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) = ((X1 ◇ X3) ◇ X3) := superpose eq104 eq105
  have eq164 (X0 X1 : G) : (X0 ◇ X1) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq147 eq56
  have eq208 (X0 X1 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq147 eq136
  have eq235 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X1)) := superpose eq14 eq7
  have eq294 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq208 eq10
  have eq295 (X0 X1 : G) : ((((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq208 eq11
  have eq297 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq208 eq7
  have eq303 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0)) := superpose eq208 eq14
  have eq308 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq57 eq303
  have eq309 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose eq308 eq297
  have eq316 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = ((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq14 eq18
  have eq318 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq18 eq18
  have eq319 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq18 eq208
  have eq323 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)))) := superpose eq18 eq14
  have eq326 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq18 eq10
  have eq338 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)))) := superpose eq147 eq323
  have eq339 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq326 eq338
  have eq342 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq339 eq319
  have eq346 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq342 eq318
  have eq347 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq339 eq346
  have eq348 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = ((X1 ◇ X1) ◇ X1) := superpose eq347 eq316
  have eq358 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) := superpose eq348 eq235
  have eq368 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq348 eq309
  have eq376 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq358 eq294
  have eq378 (X0 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq376 eq295
  have eq387 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq339 eq368
  have eq396 (X0 : G) : ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = X0 := superpose eq387 eq378
  have eq402 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ ((((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq387 eq73
  have eq408 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq387 eq164
  have eq426 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq347 eq396
  have eq427 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq347 eq426
  have eq438 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X0 ◇ ((((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq347 eq402
  have eq439 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq347 eq438
  have eq440 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq347 eq439
  have eq455 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq347 eq408
  have eq456 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq440 eq455
  have eq457 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq427 eq456
  have eq462 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X2 := superpose eq457 eq19
  have eq540 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq457 eq462
  have eq541 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq457 eq540
  have eq542 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq457 eq541
  have eq543 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq457 eq542
  have eq544 (X0 X3 : G) : X0 = X3 := superpose eq543 eq543
  have eq556 (X0 : G) : sK0 ≠ X0 := superpose eq544 eq8
  subsumption eq556 eq544


@[equational_result]
theorem Equation20710_implies_Equation2 (G : Type*) [Magma G] (h : Equation20710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X2) = (X0 ◇ ((((((X0 ◇ X2) ◇ X1) ◇ X2) ◇ X3) ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) := superpose eq11 eq11
  have eq16 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) = X0 := superpose eq11 eq11
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq11 eq11
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0)) ◇ X3)) := superpose eq11 eq7
  have eq74 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq11 eq9
  have eq91 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq74 eq74
  have eq105 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq74 eq11
  have eq126 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq11 eq91
  have eq128 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq126 eq74
  have eq135 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq128 eq16
  have eq136 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq128 eq17
  have eq160 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) := superpose eq136 eq15
  have eq184 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq136 eq105
  have eq188 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq184 eq135
  have eq193 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq184 eq160
  have eq196 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq188 eq193
  have eq199 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0)) ◇ X3)) = X1 := superpose eq196 eq21
  have eq208 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq196 eq136
  have eq268 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X3) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3)) = X1 := superpose eq208 eq199
  have eq289 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq208 eq268
  have eq302 (X0 X3 : G) : X0 = X3 := superpose eq289 eq289
  have eq316 (X0 : G) : sK0 ≠ X0 := superpose eq302 eq8
  subsumption eq316 eq302


@[equational_result]
theorem Equation20711_implies_Equation2 (G : Type*) [Magma G] (h : Equation20711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X2) ◇ (X0 ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq12
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq12
  have eq19 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X3) = X1 := superpose eq14 eq13
  have eq20 (X0 X2 X4 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X4)) = X2 := superpose eq19 eq11
  have eq31 (X0 X1 : G) : X0 = X1 := superpose eq20 eq14
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq55 eq31


@[equational_result]
theorem Equation20714_implies_Equation2 (G : Type*) [Magma G] (h : Equation20714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X2) = (X0 ◇ ((((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X0 ◇ X3) ◇ X3) ◇ X3))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X2) ◇ X2) ◇ X2))) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X3) ◇ X3) ◇ X3)) ◇ ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X3) ◇ X3) ◇ X3))) = X0 := superpose eq9 eq7
  have eq19 (X0 X1 X3 X4 X5 : G) : (X0 ◇ X1) = ((X4 ◇ (X0 ◇ X1)) ◇ ((((X1 ◇ (((X1 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X1 ◇ X3) ◇ X3) ◇ X3)) ◇ (((((X1 ◇ (((X1 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X1 ◇ X3) ◇ X3) ◇ X3)) ◇ X5) ◇ X5) ◇ X5)) ◇ (((((X1 ◇ (((X1 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X1 ◇ X3) ◇ X3) ◇ X3)) ◇ X5) ◇ X5) ◇ X5))) := superpose eq10 eq10
  have eq22 (X0 X1 X2 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) = ((X0 ◇ X1) ◇ (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ ((((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X4) ◇ X4) ◇ X4)) ◇ ((((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X4) ◇ X4) ◇ X4))) := superpose eq10 eq10
  have eq30 (X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) = X1 := superpose eq15 eq22
  have eq31 (X0 X1 X4 X5 : G) : (X0 ◇ X1) = ((X4 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (((X1 ◇ X5) ◇ X5) ◇ X5)) ◇ (((X1 ◇ X5) ◇ X5) ◇ X5))) := superpose eq30 eq19
  have eq32 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq30 eq13
  have eq38 (X0 X1 X4 : G) : (X0 ◇ X1) = ((X4 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq30 eq31
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq32 eq7
  have eq40 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X3)) := superpose eq32 eq9
  have eq41 (X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = X1 := superpose eq32 eq30
  have eq42 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq32 eq40
  have eq83 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq32 eq42
  have eq102 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq41 eq42
  have eq118 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq102 eq38
  have eq131 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq39 eq118
  have eq148 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq131 eq102
  have eq149 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq148 eq83
  have eq166 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq148 eq38
  have eq173 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq166 eq149
  have eq176 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq173 eq39
  have eq180 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq173 eq176
  have eq182 (X0 X1 : G) : X0 = X1 := superpose eq180 eq173
  have eq184 (X0 : G) : sK0 ≠ X0 := superpose eq182 eq8
  subsumption eq184 eq182


@[equational_result]
theorem Equation20715_implies_Equation2 (G : Type*) [Magma G] (h : Equation20715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation20717_implies_Equation2 (G : Type*) [Magma G] (h : Equation20717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq11 eq11
  have eq21 (X0 X2 X4 : G) : ((X2 ◇ X4) ◇ X0) = X4 := superpose eq16 eq15
  have eq25 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq21 eq16
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq25
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation20718_implies_Equation2 (G : Type*) [Magma G] (h : Equation20718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20719_implies_Equation2 (G : Type*) [Magma G] (h : Equation20719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X5) ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X0 ◇ X3) ◇ X4) ◇ X4))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ X1) ◇ ((X2 ◇ X4) ◇ X4)) := superpose eq10 eq10
  have eq24 (X0 X1 X3 X4 X5 X6 : G) : ((X1 ◇ X3) ◇ X3) = ((X0 ◇ X1) ◇ (X4 ◇ (((X4 ◇ X5) ◇ X6) ◇ X6))) := superpose eq10 eq11
  have eq42 (X1 X3 : G) : ((X1 ◇ X3) ◇ X3) = X1 := superpose eq11 eq24
  have eq46 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq42 eq15
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq42 eq46
  have eq75 (X0 X1 : G) : X0 = X1 := superpose eq42 eq58
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq94 eq75


@[equational_result]
theorem Equation20720_implies_Equation2 (G : Type*) [Magma G] (h : Equation20720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20723_implies_Equation2 (G : Type*) [Magma G] (h : Equation20723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = (X0 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) := superpose eq10 eq9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq12
  have eq19 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X3)) := superpose eq14 eq11
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq14 eq19
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq20 eq12
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq20 eq22
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq24 eq20
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation20726_implies_Equation2 (G : Type*) [Magma G] (h : Equation20726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ X2) := superpose eq10 eq9
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ X3)) := superpose eq13 eq11
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq14
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq10 eq36
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq102 eq53


@[equational_result]
theorem Equation20728_implies_Equation2 (G : Type*) [Magma G] (h : Equation20728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = (X0 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) := superpose eq10 eq7
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = (X0 ◇ X1) := superpose eq16 eq9
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq10 eq17
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := superpose eq17 eq17
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq17 eq10
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq21
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq23
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq26 eq24
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq27 eq29
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq42 eq37


@[equational_result]
theorem Equation20729_implies_Equation2 (G : Type*) [Magma G] (h : Equation20729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ ((X0 ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) = X0 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) = ((X2 ◇ X0) ◇ (X0 ◇ (((X2 ◇ X0) ◇ X4) ◇ X4))) := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X0)) ◇ X4) ◇ X4) = ((X3 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq9 eq9
  have eq30 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) = X0 := superpose eq10 eq18
  have eq33 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq30 eq21
  have eq57 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X5) = X4 := superpose eq30 eq30
  have eq67 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X4 := superpose eq30 eq30
  have eq89 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X0 := superpose eq67 eq33
  have eq109 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq89 eq57
  have eq119 (X0 X3 : G) : X0 = X3 := superpose eq109 eq109
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq139 eq119


@[equational_result]
theorem Equation20730_implies_Equation2 (G : Type*) [Magma G] (h : Equation20730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq59 eq26


@[equational_result]
theorem Equation20733_implies_Equation2 (G : Type*) [Magma G] (h : Equation20733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq11 eq10
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq23 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq15
  have eq25 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X2)) := superpose eq23 eq12
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq23 eq25
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq28 eq11
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq28 eq29
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq42 eq32


@[equational_result]
theorem Equation20736_implies_Equation2 (G : Type*) [Magma G] (h : Equation20736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ X2) = (X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X3)) = (X1 ◇ X2) := superpose eq10 eq9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq10 eq11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq10 eq12
  have eq20 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq15 eq13
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq20 eq12
  have eq26 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq20 eq23
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq26 eq26
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation20738_implies_Equation2 (G : Type*) [Magma G] (h : Equation20738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq7
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X1 := superpose eq10 eq16
  have eq25 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose eq13 eq10
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq22 eq25
  have eq27 (X0 X1 : G) : X0 = X1 := superpose eq10 eq26
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq57 eq27


@[equational_result]
theorem Equation20740_implies_Equation2 (G : Type*) [Magma G] (h : Equation20740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq60 eq27


@[equational_result]
theorem Equation20742_implies_Equation2 (G : Type*) [Magma G] (h : Equation20742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = (X0 ◇ ((((X1 ◇ X0) ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq10 eq10
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1)) := superpose eq7 eq11
  have eq28 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = ((X0 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq11 eq11
  have eq52 (X0 X3 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq18 eq10
  have eq68 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq11 eq9
  have eq74 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) ◇ X3) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0)) = (X0 ◇ (((X0 ◇ X4) ◇ (((((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) ◇ X3) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0))) ◇ X0)) := superpose eq18 eq9
  have eq87 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq7 eq52
  have eq88 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ X1) := superpose eq52 eq52
  have eq110 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) ◇ X0))) = (X0 ◇ (((X0 ◇ X4) ◇ (X0 ◇ (X0 ◇ (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) ◇ X0)))) ◇ X0)) := superpose eq87 eq74
  have eq112 (X0 X4 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X4) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq18 eq110
  have eq128 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq19
  have eq155 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq128 eq18
  have eq164 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq128 eq10
  have eq166 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq128 eq11
  have eq171 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq128 eq155
  have eq173 (X0 X4 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X4) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq171 eq112
  have eq179 (X0 X4 : G) : (X0 ◇ (((X0 ◇ X4) ◇ X0) ◇ X0)) = X0 := superpose eq171 eq173
  have eq194 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq171 eq164
  have eq195 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X0) := superpose eq171 eq166
  have eq196 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq179 eq195
  have eq197 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq171 eq196
  have eq391 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq197 eq10
  have eq421 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq171 eq391
  have eq464 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq52 eq26
  have eq508 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq197 eq464
  have eq509 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq171 eq508
  have eq510 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq509 eq28
  have eq513 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq509 eq510
  have eq516 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := superpose eq513 eq68
  have eq529 (X0 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)))) = X0 := superpose eq87 eq516
  have eq530 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq421 eq529
  have eq532 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq530 eq194
  have eq541 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq532 eq88
  have eq645 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq541 eq197
  have eq664 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq645 eq7
  have eq735 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq645 eq664
  have eq736 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq645 eq735
  have eq958 (X0 X1 : G) : X0 = X1 := superpose eq736 eq645
  have eq986 (X0 : G) : sK0 ≠ X0 := superpose eq958 eq8
  subsumption eq986 eq958


@[equational_result]
theorem Equation20744_implies_Equation2 (G : Type*) [Magma G] (h : Equation20744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X2) ◇ X5)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq23 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq12 eq10
  have eq24 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4)) := superpose eq10 eq10
  have eq33 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq10 eq12
  have eq37 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq14 eq23
  have eq38 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) := superpose eq33 eq24
  have eq82 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq37
  have eq101 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq82
  have eq118 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq101 eq38
  have eq158 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq101 eq118
  have eq159 (X0 X1 : G) : X0 = X1 := superpose eq14 eq158
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq159 eq8
  subsumption eq164 eq159


@[equational_result]
theorem Equation20746_implies_Equation2 (G : Type*) [Magma G] (h : Equation20746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = (X0 ◇ ((((X1 ◇ X0) ◇ X3) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X2 := superpose eq7 eq10
  have eq27 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X2) ◇ X2) = (X4 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X2 ◇ X4)) ◇ (X2 ◇ X4))) := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) = (((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X4) ◇ X0) ◇ X0)) := superpose eq10 eq9
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq34 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) = X3 := superpose eq9 eq7
  have eq50 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ X3) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq7 eq33
  have eq55 (X0 X1 X2 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ X2) = (((X2 ◇ X4) ◇ X2) ◇ X2) := superpose eq9 eq33
  have eq92 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) = X3 := superpose eq50 eq34
  have eq99 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) = (((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X4) ◇ X0) ◇ X0)) := superpose eq50 eq29
  have eq230 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)))) = X3 := superpose eq11 eq92
  have eq242 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)))) = X3 := superpose eq99 eq230
  have eq243 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (((X0 ◇ X2) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X2) ◇ X0) ◇ X0)))) = X3 := superpose eq99 eq242
  have eq244 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X2) ◇ X0) ◇ X0))) = X3 := superpose eq7 eq243
  have eq245 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X0))) = X3 := superpose eq99 eq244
  have eq304 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq15
  have eq324 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = (X3 ◇ ((X3 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X3)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X3))) := superpose eq15 eq11
  have eq330 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0))) := superpose eq15 eq10
  have eq350 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X2) ◇ X0) ◇ X0))) = X3 := superpose eq304 eq245
  have eq365 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) := superpose eq330 eq324
  have eq375 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X2) ◇ X0) ◇ X0)) = X3 := superpose eq365 eq350
  have eq401 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X3 ◇ X2) ◇ X3) ◇ X3)) := superpose eq11 eq375
  have eq413 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (((X2 ◇ X3) ◇ X2) ◇ X2))) = X1 := superpose eq15 eq375
  have eq448 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) = X1 := superpose eq365 eq413
  have eq449 (X0 X2 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := superpose eq448 eq401
  have eq453 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq449 eq10
  have eq530 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X2) ◇ X2) = (X4 ◇ ((X0 ◇ (X2 ◇ X4)) ◇ (X2 ◇ X4))) := superpose eq453 eq27
  have eq532 (X0 X2 X4 : G) : (((X2 ◇ X4) ◇ X2) ◇ X2) = ((X0 ◇ X2) ◇ X2) := superpose eq453 eq55
  have eq548 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq453 eq365
  have eq561 (X0 X2 X4 : G) : (X4 ◇ ((X0 ◇ (X2 ◇ X4)) ◇ (X2 ◇ X4))) = X2 := superpose eq453 eq530
  have eq562 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X2 := superpose eq453 eq532
  have eq563 (X2 X4 : G) : (X4 ◇ (X2 ◇ X4)) = X2 := superpose eq562 eq561
  have eq585 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq548 eq453
  have eq588 (X2 X4 : G) : (X4 ◇ X4) = X2 := superpose eq548 eq563
  have eq597 (X0 X1 : G) : X0 = X1 := superpose eq585 eq588
  have eq602 (X0 : G) : sK0 ≠ X0 := superpose eq597 eq8
  subsumption eq602 eq597


@[equational_result]
theorem Equation20748_implies_Equation2 (G : Type*) [Magma G] (h : Equation20748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq11
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq13 eq15
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq57 eq24


@[equational_result]
theorem Equation20752_implies_Equation2 (G : Type*) [Magma G] (h : Equation20752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq12 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation20754_implies_Equation2 (G : Type*) [Magma G] (h : Equation20754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X5) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ X5) = X2 := superpose eq11 eq10
  have eq13 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq12 eq7
  have eq15 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq13 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation20755_implies_Equation2 (G : Type*) [Magma G] (h : Equation20755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ X2) = (X0 ◇ ((((X1 ◇ X0) ◇ X4) ◇ X5) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq11
  have eq21 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X0) ◇ X4) ◇ X5) ◇ X4)) = (X2 ◇ X2) := superpose eq14 eq9
  have eq23 (X0 X2 X5 : G) : (X0 ◇ X5) = (X2 ◇ X2) := superpose eq14 eq21
  have eq24 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq11 eq23
  have eq36 (X0 X1 : G) : X0 = X1 := superpose eq11 eq24
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq70 eq36


@[equational_result]
theorem Equation20756_implies_Equation2 (G : Type*) [Magma G] (h : Equation20756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X5) ◇ X5)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X3) ◇ X4) ◇ X4))) = X2 := superpose eq7 eq7
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq50 (X0 X2 X5 : G) : (X0 ◇ ((X0 ◇ X5) ◇ X5)) = X2 := superpose eq37 eq10
  have eq73 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq37 eq50
  have eq74 (X0 X3 : G) : X0 = X3 := superpose eq73 eq73
  have eq86 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq86 eq74


@[equational_result]
theorem Equation20757_implies_Equation2 (G : Type*) [Magma G] (h : Equation20757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 X7 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X6) ◇ X7)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X6 X7 : G) : (X0 ◇ ((X0 ◇ X6) ◇ X7)) = X2 := superpose eq12 eq10
  have eq16 (X0 X2 X6 : G) : (X0 ◇ X6) = X2 := superpose eq12 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation20759_implies_Equation2 (G : Type*) [Magma G] (h : Equation20759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ X3) = ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) ◇ ((X0 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : (((X0 ◇ (X3 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq11 eq11
  have eq17 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ X0) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X0)) ◇ X0))) = X0 := superpose eq11 eq7
  have eq25 (X0 X3 X4 : G) : (X0 ◇ X3) = ((X4 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X4)) := superpose eq11 eq10
  have eq85 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq11 eq14
  have eq101 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq14 eq17
  have eq114 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq18 eq18
  have eq132 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq85 eq114
  have eq166 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq132 eq7
  have eq178 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq132 eq7
  have eq210 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq25 eq25
  have eq246 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq166 eq10
  have eq273 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq132 eq246
  have eq274 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq132 eq273
  have eq277 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq274 eq178
  have eq329 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X3 ◇ X0)) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq19 eq10
  have eq357 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X3 ◇ X0)) ◇ X0)) := superpose eq132 eq329
  have eq358 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X3 ◇ X0)) ◇ X0)) = X0 := superpose eq132 eq357
  have eq382 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq277 eq277
  have eq409 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq277 eq382
  have eq410 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq274 eq409
  have eq467 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X0)) = X0 := superpose eq410 eq358
  have eq533 (X0 X3 : G) : (X0 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X0)) = X0 := superpose eq410 eq467
  have eq534 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq533 eq101
  have eq536 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq132 eq534
  have eq637 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq17 eq410
  have eq642 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq410 eq17
  have eq652 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq637 eq210
  have eq679 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq536 eq642
  have eq683 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq679 eq652
  have eq692 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq679 eq683
  have eq693 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq679 eq692
  have eq698 (X0 X1 : G) : X0 = X1 := superpose eq693 eq679
  have eq700 (X0 : G) : sK0 ≠ X0 := superpose eq698 eq8
  subsumption eq700 eq698


@[equational_result]
theorem Equation20760_implies_Equation2 (G : Type*) [Magma G] (h : Equation20760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq7
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq14
  have eq21 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq14 eq11
  have eq23 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq17 eq21
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq23 eq11
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq24 eq23
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq45 eq32


@[equational_result]
theorem Equation20761_implies_Equation2 (G : Type*) [Magma G] (h : Equation20761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq11 eq7
  have eq17 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq14
  have eq21 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq14 eq11
  have eq23 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq17 eq21
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq23 eq11
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq24 eq23
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq45 eq32


@[equational_result]
theorem Equation20763_implies_Equation2 (G : Type*) [Magma G] (h : Equation20763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ (((X3 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)))) = X0 := superpose eq7 eq11
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = ((X4 ◇ ((X0 ◇ X3) ◇ X3)) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ X4) ◇ X4)) := superpose eq11 eq10
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) := superpose eq7 eq10
  have eq38 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) = (X0 ◇ ((X0 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ X0)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ X0))) := superpose eq11 eq25
  have eq45 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ ((X3 ◇ X0) ◇ X1)) ◇ ((X3 ◇ X0) ◇ X1)) = (X1 ◇ ((X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))))) := superpose eq25 eq25
  have eq48 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X3 ◇ X1) ◇ X2) ◇ X2) := superpose eq25 eq25
  have eq54 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X1)) = X1 := superpose eq25 eq7
  have eq58 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X2) ◇ X2)) = X1 := superpose eq25 eq7
  have eq64 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (((X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) ◇ X1) ◇ X1)) := superpose eq25 eq7
  have eq117 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = (((X4 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ X3) ◇ X3) := superpose eq7 eq48
  have eq119 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X4) ◇ X4) = (((X5 ◇ ((X1 ◇ X3) ◇ X3)) ◇ X4) ◇ X4) := superpose eq10 eq48
  have eq126 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) = (((X3 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2))) := superpose eq11 eq48
  have eq130 (X0 X1 X3 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X1) = (((X3 ◇ X1) ◇ X1) ◇ X1) := superpose eq25 eq48
  have eq171 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X2) ◇ ((X4 ◇ X1) ◇ X2)) ◇ ((X4 ◇ X1) ◇ X2)) = (X2 ◇ (((X5 ◇ (((X3 ◇ X2) ◇ ((X4 ◇ X1) ◇ X2)) ◇ ((X4 ◇ X1) ◇ X2))) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) := superpose eq48 eq9
  have eq205 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = ((X4 ◇ ((X0 ◇ X3) ◇ X3)) ◇ ((X0 ◇ X4) ◇ X4)) := superpose eq117 eq20
  have eq245 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ ((X4 ◇ X1) ◇ X2)) ◇ ((X4 ◇ X1) ◇ X2)) = (X2 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) := superpose eq117 eq171
  have eq246 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ ((X4 ◇ X1) ◇ X2)) ◇ ((X4 ◇ X1) ◇ X2)) = (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq205 eq245
  have eq266 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq205 eq205
  have eq270 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) := superpose eq7 eq205
  have eq271 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((X1 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)))) := superpose eq10 eq205
  have eq291 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = (X0 ◇ ((X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq25 eq205
  have eq292 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((X2 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq205 eq25
  have eq306 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((X1 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)))) = (((X0 ◇ X1) ◇ X3) ◇ X3) := superpose eq205 eq10
  have eq319 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq292 eq270
  have eq326 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X3) = (((X0 ◇ X1) ◇ X3) ◇ X3) := superpose eq271 eq306
  have eq328 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq326 eq130
  have eq331 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X1) ◇ X1)) := superpose eq326 eq64
  have eq333 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq326 eq7
  have eq338 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose eq326 eq14
  have eq345 (X0 X2 : G) : (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) = ((X0 ◇ X2) ◇ X2) := superpose eq326 eq25
  have eq354 (X0 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = (X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0))) := superpose eq326 eq38
  have eq365 (X0 X1 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = (((X4 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3) := superpose eq326 eq117
  have eq367 (X1 X2 X3 X4 X5 : G) : (((X5 ◇ ((X1 ◇ X3) ◇ X3)) ◇ X4) ◇ X4) = ((((X1 ◇ X2) ◇ X2) ◇ X4) ◇ X4) := superpose eq326 eq119
  have eq370 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = (((X3 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq326 eq126
  have eq378 (X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ ((X4 ◇ X1) ◇ X2)) ◇ ((X4 ◇ X1) ◇ X2)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq326 eq246
  have eq399 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) = X1 := superpose eq326 eq58
  have eq418 (X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq328 eq54
  have eq424 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) := superpose eq326 eq331
  have eq425 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq326 eq424
  have eq426 (X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq326 eq425
  have eq433 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ ((X3 ◇ X0) ◇ X1)) ◇ ((X3 ◇ X0) ◇ X1)) = (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq345 eq45
  have eq440 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ ((X3 ◇ X0) ◇ X1)) ◇ ((X3 ◇ X0) ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq345 eq433
  have eq471 (X1 X2 X4 : G) : ((X1 ◇ X4) ◇ X4) = ((((X1 ◇ X2) ◇ X2) ◇ X4) ◇ X4) := superpose eq365 eq367
  have eq478 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq378 eq440
  have eq479 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0))) := superpose eq478 eq291
  have eq481 (X0 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = (X0 ◇ (X0 ◇ (((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ X0))) := superpose eq478 eq354
  have eq482 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq478 eq345
  have eq484 (X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq478 eq426
  have eq489 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq471 eq479
  have eq493 (X0 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq365 eq481
  have eq494 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq482 eq493
  have eq495 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq494 eq338
  have eq498 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = (((X3 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq494 eq370
  have eq514 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) = X1 := superpose eq471 eq399
  have eq539 (X0 X1 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq333 eq333
  have eq570 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X0 := superpose eq418 eq539
  have eq587 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq514 eq570
  have eq588 (X0 : G) : (((X0 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ X0) = X0 := superpose eq489 eq587
  have eq589 (X0 : G) : (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X0) = X0 := superpose eq471 eq588
  have eq590 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq494 eq589
  have eq591 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq326 eq590
  have eq621 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) := superpose eq591 eq205
  have eq632 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose eq326 eq621
  have eq633 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq632 eq495
  have eq634 (X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = X1 := superpose eq633 eq484
  have eq637 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ X0) := superpose eq634 eq319
  have eq665 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq637 eq498
  have eq673 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq665 eq591
  have eq679 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq673 eq665
  have eq681 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq679 eq637
  have eq688 (X1 X3 : G) : ((X1 ◇ X3) ◇ X3) = X1 := superpose eq681 eq326
  have eq690 (X0 X4 : G) : ((X4 ◇ X0) ◇ ((X0 ◇ X4) ◇ X4)) = X0 := superpose eq688 eq205
  have eq691 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq688 eq266
  have eq732 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X0 := superpose eq688 eq690
  have eq733 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq688 eq691
  have eq735 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq733 eq681
  have eq737 (X0 X4 : G) : (X4 ◇ X0) = X0 := superpose eq735 eq732
  have eq740 (X0 X1 : G) : X0 = X1 := superpose eq737 eq735
  have eq750 (X0 : G) : sK0 ≠ X0 := superpose eq740 eq8
  subsumption eq750 eq740


@[equational_result]
theorem Equation20765_implies_Equation2 (G : Type*) [Magma G] (h : Equation20765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq12
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq12
  have eq19 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X1) ◇ X3) = X1 := superpose eq14 eq13
  have eq20 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X4)) = X0 := superpose eq19 eq11
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq14 eq20
  have eq36 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq33 eq19
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq12 eq36
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq56 eq37


@[equational_result]
theorem Equation20768_implies_Equation2 (G : Type*) [Magma G] (h : Equation20768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ (((X3 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ (((X3 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3))) := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) = ((X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) ◇ ((X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)))) := superpose eq11 eq11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) = ((X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) := superpose eq10 eq15
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ (((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X3) ◇ X3)) := superpose eq7 eq9
  have eq27 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) := superpose eq7 eq9
  have eq73 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) ◇ X1) ◇ X1) = ((X3 ◇ (((X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) ◇ X1) ◇ X1)) ◇ (((X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X0) ◇ X0)) := superpose eq11 eq10
  have eq85 (X0 X1 X3 X4 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) ◇ (((X4 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) ◇ X4) ◇ X4))) := superpose eq10 eq11
  have eq138 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)))) := superpose eq7 eq27
  have eq157 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (((X3 ◇ X2) ◇ X3) ◇ X3)) = X2 := superpose eq27 eq7
  have eq162 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (X2 ◇ (((X3 ◇ X2) ◇ X3) ◇ X3))) = X2 := superpose eq27 eq11
  have eq181 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) = X0 := superpose eq11 eq138
  have eq182 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ X2) := superpose eq181 eq9
  have eq183 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ X2)) := superpose eq181 eq12
  have eq195 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) ◇ X1) ◇ X1) = ((X3 ◇ (((X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) ◇ X1) ◇ X1)) ◇ X2) := superpose eq181 eq73
  have eq197 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq181 eq22
  have eq201 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) := superpose eq181 eq85
  have eq218 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq182 eq7
  have eq219 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) := superpose eq182 eq10
  have eq225 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2)) := superpose eq182 eq21
  have eq264 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq182 eq183
  have eq277 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = ((X3 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X2) := superpose eq181 eq195
  have eq278 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ (X0 ◇ X2)) ◇ X2) := superpose eq182 eq277
  have eq281 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ (X1 ◇ X0)) := superpose eq182 eq197
  have eq283 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) = ((X1 ◇ X0) ◇ (((X1 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) := superpose eq182 eq201
  have eq294 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (X2 ◇ X3)) = X2 := superpose eq182 eq157
  have eq295 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) = X2 := superpose eq264 eq294
  have eq298 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X3) := superpose eq295 eq219
  have eq306 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X0)) = X1 := superpose eq295 eq281
  have eq308 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X3 ◇ X1))) = X3 := superpose eq295 eq283
  have eq314 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq298 eq181
  have eq325 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (X2 ◇ X3)) = X2 := superpose eq314 eq162
  have eq326 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq306 eq325
  have eq327 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq326 eq225
  have eq330 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X3 := superpose eq327 eq308
  have eq331 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq330 eq278
  have eq332 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq331 eq218
  have eq342 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq331 eq332
  have eq346 (X0 X1 : G) : X0 = X1 := superpose eq342 eq331
  have eq348 (X0 : G) : sK0 ≠ X0 := superpose eq346 eq8
  subsumption eq348 eq346


@[equational_result]
theorem Equation20769_implies_Equation2 (G : Type*) [Magma G] (h : Equation20769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20771_implies_Equation2 (G : Type*) [Magma G] (h : Equation20771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) = X2 := superpose eq11 eq7
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq7 eq12
  have eq39 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (((X5 ◇ X2) ◇ X6) ◇ ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0)) ◇ X0))) = X2 := superpose eq12 eq7
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq30 eq18
  have eq57 (X0 X2 X6 : G) : (X0 ◇ X6) = X2 := superpose eq40 eq39
  have eq58 (X0 X2 : G) : X0 = X2 := superpose eq11 eq57
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq85 eq58


@[equational_result]
theorem Equation20772_implies_Equation2 (G : Type*) [Magma G] (h : Equation20772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20773_implies_Equation2 (G : Type*) [Magma G] (h : Equation20773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = (X0 ◇ (((X4 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ X5) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ ((X0 ◇ X5) ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (((X3 ◇ X0) ◇ X4) ◇ X4))) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 X3 X4 X5 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = (X0 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ (((X4 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ X5) ◇ X5))) := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 X5 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) = ((X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3))) ◇ ((X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ ((X0 ◇ X5) ◇ X5))) := superpose eq11 eq11
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) = ((X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3))) ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) := superpose eq10 eq15
  have eq28 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ ((X0 ◇ X4) ◇ X4)) := superpose eq7 eq9
  have eq31 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (((X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ X5) ◇ X5)))) := superpose eq11 eq9
  have eq50 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) = ((X2 ◇ X0) ◇ (X0 ◇ (((X4 ◇ X0) ◇ X5) ◇ X5))) := superpose eq7 eq28
  have eq65 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X4) = (X3 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X2 ◇ X3) ◇ X4) ◇ X4))) := superpose eq28 eq9
  have eq66 (X0 X1 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X4 ◇ X3) ◇ X5) ◇ X5)) = X3 := superpose eq28 eq7
  have eq83 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) = X0 := superpose eq11 eq50
  have eq92 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2))) := superpose eq83 eq31
  have eq93 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = (X0 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X3)) := superpose eq83 eq12
  have eq97 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (X1 ◇ X2) := superpose eq7 eq92
  have eq98 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq97 eq7
  have eq105 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((X1 ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X3)) := superpose eq97 eq21
  have eq115 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = (X0 ◇ (X3 ◇ X3)) := superpose eq97 eq93
  have eq116 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X3 ◇ X3)) := superpose eq97 eq115
  have eq130 (X0 X1 X3 X4 : G) : (X3 ◇ X4) = (X3 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X3 ◇ X4))) := superpose eq97 eq65
  have eq131 (X0 X1 X3 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X3 ◇ X5)) = X3 := superpose eq97 eq66
  have eq132 (X3 X4 : G) : (X3 ◇ X4) = (X3 ◇ X3) := superpose eq131 eq130
  have eq143 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) := superpose eq132 eq105
  have eq144 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = (X0 ◇ X0) := superpose eq116 eq143
  have eq145 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq98 eq144
  have eq147 (X3 X4 : G) : (X3 ◇ X4) = X3 := superpose eq145 eq132
  have eq154 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = (X0 ◇ (X0 ◇ X4)) := superpose eq147 eq28
  have eq165 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq147 eq154
  have eq166 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq147 eq165
  have eq167 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq147 eq166
  have eq168 (X0 X1 : G) : X0 = X1 := superpose eq145 eq167
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq168 eq8
  subsumption eq173 eq168


@[equational_result]
theorem Equation20774_implies_Equation2 (G : Type*) [Magma G] (h : Equation20774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20776_implies_Equation2 (G : Type*) [Magma G] (h : Equation20776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X0) ◇ X1) = (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X3) ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = ((X3 ◇ ((X0 ◇ X3) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1))) ◇ (X3 ◇ X3)) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = (((X2 ◇ X2) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq11 eq11
  have eq30 (X0 X1 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq10
  have eq39 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq30 eq30
  have eq40 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq30 eq30
  have eq43 (X0 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq30 eq10
  have eq55 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq40 eq39
  have eq56 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = (((X2 ◇ X2) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) ◇ (X2 ◇ X2)) := superpose eq55 eq15
  have eq61 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = ((X3 ◇ ((X0 ◇ X3) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1))) ◇ X3) := superpose eq55 eq12
  have eq72 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = ((X2 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) ◇ X2) := superpose eq55 eq56
  have eq73 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = ((X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X2) := superpose eq55 eq72
  have eq90 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ (((X2 ◇ X0) ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq30 eq9
  have eq97 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X0) = (((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) ◇ (((X4 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2))))) := superpose eq10 eq9
  have eq98 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq30 eq9
  have eq113 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq90
  have eq138 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) ◇ (((X4 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)))) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2))))) = X0 := superpose eq55 eq97
  have eq139 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ ((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2))) ◇ X0)))) = X0 := superpose eq113 eq138
  have eq140 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) ◇ (X0 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2))))) = X0 := superpose eq61 eq139
  have eq141 (X0 X2 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq55 eq98
  have eq209 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq43 eq43
  have eq244 (X0 X1 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq43 eq73
  have eq248 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq55 eq73
  have eq260 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)))) = X2 := superpose eq73 eq43
  have eq266 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq55 eq244
  have eq290 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq141 eq73
  have eq314 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq55 eq290
  have eq420 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq314 eq43
  have eq560 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)))) := superpose eq7 eq420
  have eq598 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq260 eq560
  have eq599 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq598 eq266
  have eq601 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq598 eq7
  have eq631 (X0 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ (X0 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3)))) = X0 := superpose eq598 eq140
  have eq741 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq601 eq248
  have eq748 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq601 eq741
  have eq749 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq748 eq209
  have eq751 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq55 eq749
  have eq763 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq751 eq599
  have eq849 (X0 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3))) = X0 := superpose eq763 eq631
  have eq850 (X0 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq763 eq849
  have eq851 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq763 eq850
  have eq959 (X0 X2 : G) : X0 = X2 := superpose eq851 eq851
  have eq964 (X0 : G) : sK0 ≠ X0 := superpose eq959 eq8
  subsumption eq964 eq959


@[equational_result]
theorem Equation20778_implies_Equation2 (G : Type*) [Magma G] (h : Equation20778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X0) ◇ X3) = (X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X3)) := superpose eq7 eq12
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq15 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq12 eq7
  have eq20 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq14 eq15
  have eq21 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X6) ◇ ((X4 ◇ X6) ◇ X7)) = X6 := superpose eq7 eq10
  have eq30 (X0 X3 X4 X5 X6 : G) : ((X3 ◇ X0) ◇ X5) = (X0 ◇ ((X4 ◇ ((X3 ◇ X0) ◇ X5)) ◇ X6)) := superpose eq10 eq10
  have eq32 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X4)) = X0 := superpose eq12 eq10
  have eq44 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X0) ◇ X3) = X0 := superpose eq32 eq13
  have eq49 (X4 X5 X6 X7 : G) : (X5 ◇ ((X4 ◇ X6) ◇ X7)) = X6 := superpose eq44 eq21
  have eq53 (X0 X3 X5 X6 : G) : ((X3 ◇ X0) ◇ X5) = (X0 ◇ (X0 ◇ X6)) := superpose eq49 eq30
  have eq54 (X0 X3 X5 : G) : ((X3 ◇ X0) ◇ X5) = X0 := superpose eq20 eq53
  have eq58 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq54 eq44
  have eq64 (X0 X1 : G) : X0 = X1 := superpose eq14 eq58
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq69 eq64


@[equational_result]
theorem Equation20780_implies_Equation2 (G : Type*) [Magma G] (h : Equation20780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X4 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ X3)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ X3)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ X3))) = ((X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = (X2 ◇ (((X3 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2))) := superpose eq7 eq9
  have eq27 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose eq9 eq9
  have eq28 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)))) = X3 := superpose eq9 eq7
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X2)) = X3 := superpose eq9 eq7
  have eq34 (X0 X1 X2 : G) : ((X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) = ((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) := superpose eq15 eq12
  have eq44 (X0 X1 X2 X3 : G) : ((((X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ X3) ◇ (((X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)))) = X3 := superpose eq7 eq11
  have eq60 (X1 X2 X3 : G) : ((((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ X3) ◇ (((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ ((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)))) = X3 := superpose eq34 eq44
  have eq61 (X1 X2 X3 : G) : ((((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ X3) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) = X3 := superpose eq11 eq60
  have eq82 (X0 X1 X2 X4 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X2) = (((X4 ◇ X2) ◇ X2) ◇ X2) := superpose eq9 eq27
  have eq115 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X2 ◇ X1) ◇ X1) ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1))) = X1 := superpose eq27 eq11
  have eq161 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((((X3 ◇ X1) ◇ X1) ◇ X1) ◇ (((X4 ◇ X0) ◇ X0) ◇ X0))) = X2 := superpose eq7 eq28
  have eq177 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)))) = (X3 ◇ (((X4 ◇ ((X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X3)) ◇ ((X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X3)) ◇ ((X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X3))) := superpose eq28 eq9
  have eq182 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (((X5 ◇ ((X2 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ X4)) ◇ ((X2 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ X4)) ◇ ((X2 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ X4))) = ((X0 ◇ (X2 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) ◇ (X2 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) := superpose eq28 eq9
  have eq197 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) ◇ (X2 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) = ((X2 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ (X2 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) := superpose eq177 eq182
  have eq216 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1)))) ◇ (X1 ◇ (((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1))))) ◇ X1)) = X2 := superpose eq28 eq29
  have eq266 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1)) ◇ ((X1 ◇ (((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1))) ◇ (X1 ◇ (((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1)) ◇ (X4 ◇ X1))))) ◇ X1)) = X2 := superpose eq197 eq216
  have eq428 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) = (X0 ◇ ((((X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X4 ◇ X0) ◇ X0) ◇ X0))) := superpose eq11 eq161
  have eq478 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq161
  have eq516 (X0 X1 X2 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) = (X0 ◇ (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X4 ◇ X0) ◇ X0) ◇ X0))) := superpose eq34 eq428
  have eq592 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = (X0 ◇ (((X1 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X3) ◇ X0)) ◇ ((((X2 ◇ X3) ◇ X3) ◇ X3) ◇ X0)) ◇ ((((X2 ◇ X3) ◇ X3) ◇ X3) ◇ X0))) := superpose eq9 eq61
  have eq658 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq592 eq15
  have eq660 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X1) ◇ X1) = ((X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) := superpose eq658 eq34
  have eq670 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) = X1 := superpose eq658 eq115
  have eq691 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ X2) = (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (((X4 ◇ X0) ◇ X0) ◇ X0))) := superpose eq658 eq516
  have eq710 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq670 eq658
  have eq711 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq710 eq7
  have eq712 (X0 X1 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := superpose eq710 eq9
  have eq719 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X2) = X2 := superpose eq710 eq82
  have eq778 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq710 eq660
  have eq808 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (((X4 ◇ X1) ◇ ((X1 ◇ (X4 ◇ X1)) ◇ (X1 ◇ (X4 ◇ X1)))) ◇ X1)) = X2 := superpose eq710 eq266
  have eq839 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq710 eq712
  have eq840 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq839 eq478
  have eq851 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X2) = X2 := superpose eq710 eq719
  have eq852 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq839 eq851
  have eq1054 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X4 ◇ X1)) ◇ (X1 ◇ (X4 ◇ X1)))) = X2 := superpose eq840 eq808
  have eq1055 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X4 ◇ X1))) = X2 := superpose eq852 eq1054
  have eq1056 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X4) = X2 := superpose eq839 eq1055
  have eq1057 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq1056 eq840
  have eq1093 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X2) = (X0 ◇ X2) := superpose eq1056 eq691
  have eq1094 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq778 eq1093
  have eq1095 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1094 eq711
  have eq1253 (X0 X1 : G) : X0 = X1 := superpose eq1095 eq1057
  have eq1266 (X0 : G) : sK0 ≠ X0 := superpose eq1253 eq8
  subsumption eq1266 eq1253


@[equational_result]
theorem Equation20782_implies_Equation2 (G : Type*) [Magma G] (h : Equation20782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq12
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq12
  have eq19 (X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X1) ◇ X3) = X1 := superpose eq14 eq13
  have eq20 (X1 X3 X4 : G) : ((X1 ◇ X3) ◇ (X1 ◇ X4)) = X3 := superpose eq19 eq11
  have eq26 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq12 eq20
  have eq27 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq20 eq20
  have eq31 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq26 eq27
  have eq32 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X1 := superpose eq31 eq19
  have eq38 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq31 eq32
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq38 eq38
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq44 eq39


@[equational_result]
theorem Equation20786_implies_Equation2 (G : Type*) [Magma G] (h : Equation20786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation20788_implies_Equation2 (G : Type*) [Magma G] (h : Equation20788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ ((X0 ◇ X5) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X3) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ X1) := superpose eq11 eq11
  have eq18 (X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X3) ◇ X1) = (X1 ◇ X1) := superpose eq13 eq12
  have eq19 (X0 X2 X4 X5 : G) : (((X2 ◇ X2) ◇ X4) ◇ ((X0 ◇ X5) ◇ (X2 ◇ X2))) = X4 := superpose eq18 eq10
  have eq30 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq11 eq19
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq11 eq30
  have eq51 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq42 eq30
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq11 eq51
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq80 eq56


@[equational_result]
theorem Equation20789_implies_Equation2 (G : Type*) [Magma G] (h : Equation20789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X4) ◇ (X1 ◇ X0))) = X3 := superpose eq11 eq7
  have eq54 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ X2)) = X3 := superpose eq11 eq14
  have eq79 (X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ X4) = X3 := superpose eq54 eq17
  have eq85 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq79 eq7
  have eq112 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq85 eq14
  have eq122 (X0 X2 : G) : X0 = X2 := superpose eq11 eq112
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq8
  subsumption eq154 eq122


@[equational_result]
theorem Equation20790_implies_Equation2 (G : Type*) [Magma G] (h : Equation20790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (((X3 ◇ X2) ◇ X4) ◇ X4))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3)) = X4 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X5) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ X4))) = X5 := superpose eq11 eq7
  have eq26 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) = (X0 ◇ (((X5 ◇ (X1 ◇ X0)) ◇ X6) ◇ X6)) := superpose eq11 eq7
  have eq33 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X5) ◇ X5)) = X2 := superpose eq7 eq12
  have eq50 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (((X5 ◇ (X1 ◇ X0)) ◇ X6) ◇ X6)) = (((X2 ◇ (X3 ◇ X1)) ◇ X4) ◇ X4) := superpose eq12 eq7
  have eq51 (X1 X5 : G) : ((X1 ◇ X5) ◇ X1) = X5 := superpose eq33 eq24
  have eq60 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq51
  have eq61 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq51 eq51
  have eq76 (X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) = X1 := superpose eq61 eq60
  have eq83 (X0 X1 X5 X6 : G) : (X0 ◇ (((X5 ◇ (X1 ◇ X0)) ◇ X6) ◇ X6)) = X1 := superpose eq76 eq26
  have eq86 (X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X1)) ◇ X4) ◇ X4) = X1 := superpose eq83 eq50
  have eq90 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq86 eq83
  have eq110 (X0 X2 : G) : X0 = X2 := superpose eq90 eq90
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq110 eq8
  subsumption eq112 eq110


@[equational_result]
theorem Equation20791_implies_Equation2 (G : Type*) [Magma G] (h : Equation20791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20794_implies_Equation2 (G : Type*) [Magma G] (h : Equation20794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ X2) = (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) := superpose eq7 eq12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq18 (X0 X2 : G) : (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) = X0 := superpose eq12 eq7
  have eq23 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq15 eq14
  have eq27 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq18
  have eq28 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq27 eq23
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq28 eq12
  have eq41 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq38 eq28
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq41 eq38
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq56 eq43


@[equational_result]
theorem Equation20795_implies_Equation2 (G : Type*) [Magma G] (h : Equation20795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X3)) := superpose eq7 eq12
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq17 (X0 X2 X3 : G) : (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X3)) = X0 := superpose eq12 eq7
  have eq18 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq14 eq13
  have eq23 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq14 eq17
  have eq24 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq23 eq18
  have eq31 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq24
  have eq39 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq31 eq24
  have eq41 (X0 X1 : G) : X0 = X1 := superpose eq14 eq39
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq49 eq41


@[equational_result]
theorem Equation20799_implies_Equation2 (G : Type*) [Magma G] (h : Equation20799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq11
  have eq17 (X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X1) ◇ X3) = X1 := superpose eq13 eq12
  have eq18 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X0 ◇ X4)) = X3 := superpose eq17 eq10
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq11 eq18
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq18 eq18
  have eq28 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq23 eq24
  have eq29 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X1 := superpose eq28 eq17
  have eq34 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq28 eq29
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq40 eq35


@[equational_result]
theorem Equation20802_implies_Equation2 (G : Type*) [Magma G] (h : Equation20802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq14 eq14
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq14 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation20803_implies_Equation2 (G : Type*) [Magma G] (h : Equation20803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq12 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation20805_implies_Equation2 (G : Type*) [Magma G] (h : Equation20805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq11 eq11
  have eq21 (X0 X2 X4 : G) : ((X2 ◇ X4) ◇ X0) = X4 := superpose eq16 eq15
  have eq27 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq21 eq16
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq27
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation20806_implies_Equation2 (G : Type*) [Magma G] (h : Equation20806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X4) ◇ (((X0 ◇ X0) ◇ X3) ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X4) = X2 := superpose eq7 eq10
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq13 eq17
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq41 eq28


@[equational_result]
theorem Equation20807_implies_Equation2 (G : Type*) [Magma G] (h : Equation20807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X3 ◇ X3) ◇ X4) ◇ X4))) = X2 := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq59 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq35 eq35
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq35 eq59
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq83 eq70


@[equational_result]
theorem Equation20808_implies_Equation2 (G : Type*) [Magma G] (h : Equation20808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20810_implies_Equation2 (G : Type*) [Magma G] (h : Equation20810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X0) ◇ X1) = (X0 ◇ (((X4 ◇ X5) ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X0) ◇ X4) = ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq12
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq7
  have eq51 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq32 eq10
  have eq102 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq32 eq37
  have eq106 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq37 eq10
  have eq119 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq37 eq32
  have eq120 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq119 eq102
  have eq122 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq32 eq120
  have eq125 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq122 eq51
  have eq206 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq122 eq10
  have eq208 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) := superpose eq122 eq9
  have eq292 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X0)) ◇ X4) = ((X0 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X0)) ◇ X4)) ◇ X0) := superpose eq106 eq11
  have eq372 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq125 eq11
  have eq387 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq125 eq37
  have eq406 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq122 eq372
  have eq407 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq122 eq406
  have eq408 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X2 ◇ (((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) := superpose eq407 eq208
  have eq412 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq125 eq387
  have eq417 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq412 eq206
  have eq420 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq417 eq408
  have eq434 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X4) = ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X4)) ◇ X0) := superpose eq420 eq292
  have eq437 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq420 eq10
  have eq509 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X4) = X0 := superpose eq420 eq434
  have eq510 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq420 eq509
  have eq522 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq510 eq437
  have eq528 (X0 X2 : G) : X0 = X2 := superpose eq522 eq522
  have eq533 (X0 : G) : sK0 ≠ X0 := superpose eq528 eq8
  subsumption eq533 eq528


@[equational_result]
theorem Equation20811_implies_Equation2 (G : Type*) [Magma G] (h : Equation20811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq12 eq7
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq12 eq10
  have eq42 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq12 eq16
  have eq49 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq16 eq12
  have eq51 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq42 eq49
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X2 := superpose eq51 eq29
  have eq60 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq51 eq52
  have eq61 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq51 eq60
  have eq62 (X0 X1 : G) : X0 = X1 := superpose eq14 eq61
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq67 eq62


@[equational_result]
theorem Equation20812_implies_Equation2 (G : Type*) [Magma G] (h : Equation20812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X3) = (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) := superpose eq7 eq12
  have eq18 (X0 X2 X3 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) = X0 := superpose eq12 eq7
  have eq21 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X3) = X0 := superpose eq18 eq13
  have eq30 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq21 eq21
  have eq37 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq30 eq21
  have eq42 (X0 X2 : G) : X0 = X2 := superpose eq37 eq37
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq47 eq42


@[equational_result]
theorem Equation20813_implies_Equation2 (G : Type*) [Magma G] (h : Equation20813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X7)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X0) ◇ X4) = (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) := superpose eq7 eq12
  have eq18 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) = X0 := superpose eq12 eq7
  have eq19 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X0) ◇ X4) = X0 := superpose eq18 eq13
  have eq25 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq12 eq10
  have eq31 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq10 eq12
  have eq32 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq25 eq31
  have eq36 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq32 eq19
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq12 eq36
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq50 eq40


@[equational_result]
theorem Equation20815_implies_Equation2 (G : Type*) [Magma G] (h : Equation20815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X1) ◇ X1) = (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq10 eq10
  have eq27 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (((X5 ◇ X6) ◇ ((((X2 ◇ X3) ◇ X1) ◇ X1) ◇ X4)) ◇ ((((X2 ◇ X3) ◇ X1) ◇ X1) ◇ X4))) = (X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X1)) := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (((X4 ◇ X5) ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) ◇ (((X2 ◇ X1) ◇ X1) ◇ X3))) = (X0 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq10 eq9
  have eq39 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)) = (X4 ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4))) := superpose eq10 eq9
  have eq45 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (((X3 ◇ X4) ◇ X5) ◇ X5) = ((((X6 ◇ X7) ◇ (X2 ◇ X5)) ◇ (X2 ◇ X5)) ◇ (((X8 ◇ X9) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) := superpose eq9 eq9
  have eq50 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)))) = X4 := superpose eq9 eq7
  have eq64 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq18 eq18
  have eq65 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq7 eq18
  have eq78 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X4) = (X0 ◇ (((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X4) ◇ X0)) ◇ (((X3 ◇ X4) ◇ X4) ◇ X0))) := superpose eq9 eq18
  have eq93 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X3 ◇ X4) ◇ X5) ◇ X5) = ((((X6 ◇ X7) ◇ (X2 ◇ X5)) ◇ (X2 ◇ X5)) ◇ (X2 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2))) := superpose eq65 eq45
  have eq94 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X3 ◇ X4) ◇ X5) ◇ X5) = ((((X6 ◇ X7) ◇ (X2 ◇ X5)) ◇ (X2 ◇ X5)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq64 eq93
  have eq95 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X1) ◇ X1) = (X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X1)) := superpose eq78 eq27
  have eq96 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X0 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq78 eq28
  have eq100 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = X4 := superpose eq95 eq50
  have eq117 (X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)) = (X4 ◇ ((X3 ◇ X4) ◇ X4)) := superpose eq96 eq39
  have eq123 (X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)) = ((X3 ◇ X4) ◇ X4) := superpose eq96 eq117
  have eq131 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X5) ◇ X5) = (((X2 ◇ X5) ◇ X5) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq123 eq94
  have eq134 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X3 ◇ X0) ◇ X0)) = X4 := superpose eq123 eq100
  have eq243 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (((X3 ◇ X4) ◇ X1) ◇ X1))) = X2 := superpose eq7 eq134
  have eq273 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (((X3 ◇ X4) ◇ X1) ◇ X1)) = X2 := superpose eq95 eq243
  have eq274 (X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X5) ◇ X5) = X5 := superpose eq273 eq131
  have eq278 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq274 eq95
  have eq297 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq278 eq10
  have eq318 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq278 eq297
  have eq351 (X0 X1 : G) : X0 = X1 := superpose eq318 eq278
  have eq361 (X0 : G) : sK0 ≠ X0 := superpose eq351 eq8
  subsumption eq361 eq351


@[equational_result]
theorem Equation20816_implies_Equation2 (G : Type*) [Magma G] (h : Equation20816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X1) ◇ X2) = (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X0)) ◇ X4)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X4) ◇ (X0 ◇ X3)) = X4 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X0)) ◇ X4)) = ((X2 ◇ X1) ◇ (X3 ◇ X2)) := superpose eq10 eq7
  have eq29 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X0)) = X4 := superpose eq11 eq11
  have eq33 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X5) ◇ X3)) ◇ X1) ◇ X6) ◇ X0) = X6 := superpose eq7 eq11
  have eq48 (X0 X1 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X0)) ◇ X4)) = X1 := superpose eq29 eq22
  have eq52 (X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X1) ◇ X2) = X1 := superpose eq48 eq9
  have eq61 (X0 X3 X4 X5 X6 : G) : (((((X3 ◇ X4) ◇ X5) ◇ X3) ◇ X6) ◇ X0) = X6 := superpose eq52 eq33
  have eq62 (X0 X5 X6 : G) : ((X5 ◇ X6) ◇ X0) = X6 := superpose eq52 eq61
  have eq66 (X1 X2 X3 : G) : (X3 ◇ X2) = X1 := superpose eq62 eq52
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq66 eq66
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq71 eq69


@[equational_result]
theorem Equation20817_implies_Equation2 (G : Type*) [Magma G] (h : Equation20817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X1) ◇ X3) = (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X0)) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (((X4 ◇ X5) ◇ X3) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ (X0 ◇ X0)) = X4 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X3 ◇ X4) ◇ X5) ◇ X4) ◇ X6) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X6 := superpose eq11 eq11
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq7
  have eq46 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X4) ◇ X5) ◇ X4)) = (X0 ◇ (((X6 ◇ X7) ◇ (X1 ◇ X0)) ◇ X7)) := superpose eq10 eq7
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X4) ◇ X5) ◇ X4)) = (X0 ◇ (X1 ◇ X0)) := superpose eq10 eq20
  have eq51 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq20 eq20
  have eq63 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X4) ◇ X5) ◇ X4)) = X1 := superpose eq51 eq49
  have eq71 (X0 X1 X6 X7 : G) : (X0 ◇ (((X6 ◇ X7) ◇ (X1 ◇ X0)) ◇ X7)) = X1 := superpose eq63 eq46
  have eq75 (X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X1) ◇ X3) = X1 := superpose eq71 eq9
  have eq78 (X2 X3 X4 X5 X6 : G) : (((((X3 ◇ X4) ◇ X5) ◇ X4) ◇ X6) ◇ X2) = X6 := superpose eq75 eq19
  have eq87 (X2 X5 X6 : G) : ((X5 ◇ X6) ◇ X2) = X6 := superpose eq75 eq78
  have eq90 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq87 eq75
  have eq95 (X0 X2 : G) : X0 = X2 := superpose eq90 eq90
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq100 eq95


@[equational_result]
theorem Equation20818_implies_Equation2 (G : Type*) [Magma G] (h : Equation20818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ (X0 ◇ X6)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X1) ◇ X4) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq12
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq12
  have eq19 (X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X1) ◇ X4) = X1 := superpose eq14 eq13
  have eq20 (X0 X3 X5 X6 : G) : ((X3 ◇ X5) ◇ (X0 ◇ X6)) = X5 := superpose eq19 eq11
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq12 eq20
  have eq30 (X1 X3 X4 : G) : (X3 ◇ X4) = X1 := superpose eq27 eq19
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq12 eq30
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq57 eq32


@[equational_result]
theorem Equation20820_implies_Equation2 (G : Type*) [Magma G] (h : Equation20820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X2) ◇ X1) = (X0 ◇ (((X4 ◇ X5) ◇ X4) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X5 ◇ X4)) ◇ (X1 ◇ X0))) = ((X2 ◇ (X3 ◇ X2)) ◇ X1) := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ X4) ◇ (X1 ◇ X0))) = ((X2 ◇ (X3 ◇ X2)) ◇ X1) := superpose eq10 eq7
  have eq27 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X2 ◇ X3) ◇ X2)) = X4 := superpose eq7 eq11
  have eq29 (X0 X1 X2 X5 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X5) ◇ X2) = X5 := superpose eq11 eq11
  have eq36 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ (X6 ◇ X5)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X4)) ◇ X0))) = X3 := superpose eq11 eq10
  have eq42 (X0 X3 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ (X6 ◇ X5)) ◇ (X3 ◇ X4))) = X3 := superpose eq29 eq36
  have eq43 (X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X1) = X1 := superpose eq42 eq13
  have eq45 (X0 X1 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ X4) ◇ (X1 ◇ X0))) = X1 := superpose eq43 eq20
  have eq51 (X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X1) = X1 := superpose eq45 eq9
  have eq52 (X2 X5 : G) : (X5 ◇ X2) = X5 := superpose eq51 eq29
  have eq56 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X2 ◇ X3)) = X4 := superpose eq52 eq27
  have eq63 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ X2) = X4 := superpose eq52 eq56
  have eq64 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq52 eq63
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq64 eq64
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq70 eq65


@[equational_result]
theorem Equation20821_implies_Equation2 (G : Type*) [Magma G] (h : Equation20821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X3 ◇ X4) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq71 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq37 eq37
  have eq76 (X0 X3 : G) : X0 = X3 := superpose eq71 eq71
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq113 eq76


@[equational_result]
theorem Equation20822_implies_Equation2 (G : Type*) [Magma G] (h : Equation20822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20823_implies_Equation2 (G : Type*) [Magma G] (h : Equation20823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20825_implies_Equation2 (G : Type*) [Magma G] (h : Equation20825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X5) ◇ X3)) = X4 := superpose eq7 eq11
  have eq22 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ ((X4 ◇ X5) ◇ X5)) ◇ X6) ◇ X0) = X6 := superpose eq11 eq11
  have eq35 (X0 X1 X2 X6 X7 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X7) ◇ X6) = X7 := superpose eq12 eq12
  have eq52 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ X5) = X4 := superpose eq35 eq17
  have eq53 (X0 X4 X5 X6 : G) : (((X4 ◇ X5) ◇ X5) ◇ X0) = X6 := superpose eq35 eq22
  have eq74 (X0 X5 X6 : G) : (X5 ◇ X0) = X6 := superpose eq52 eq53
  have eq75 (X0 X3 : G) : X0 = X3 := superpose eq74 eq74
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq87 eq75


@[equational_result]
theorem Equation20826_implies_Equation2 (G : Type*) [Magma G] (h : Equation20826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq12 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation20827_implies_Equation2 (G : Type*) [Magma G] (h : Equation20827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X3 := superpose eq7 eq7
  have eq14 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X3 := superpose eq7 eq11
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq14 eq14
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq14 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation20828_implies_Equation2 (G : Type*) [Magma G] (h : Equation20828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq12 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation20830_implies_Equation2 (G : Type*) [Magma G] (h : Equation20830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X0) = X5 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq11 eq11
  have eq21 (X0 X3 X5 : G) : ((X3 ◇ X5) ◇ X0) = X5 := superpose eq16 eq15
  have eq27 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq21 eq16
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq27
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation20831_implies_Equation2 (G : Type*) [Magma G] (h : Equation20831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X7 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X7) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X7 : G) : ((X1 ◇ X2) ◇ X7) = X2 := superpose eq11 eq10
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq13 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20832_implies_Equation2 (G : Type*) [Magma G] (h : Equation20832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 X6 X7 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X7) ◇ (((X4 ◇ X5) ◇ X6) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X7 : G) : ((X1 ◇ X2) ◇ X7) = X2 := superpose eq7 eq10
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq13 eq17
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq41 eq28


@[equational_result]
theorem Equation20833_implies_Equation2 (G : Type*) [Magma G] (h : Equation20833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X4 ◇ X5) ◇ X6) ◇ X6))) = X2 := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq65 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq35 eq35
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq65 eq65
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq107 eq70


@[equational_result]
theorem Equation20834_implies_Equation2 (G : Type*) [Magma G] (h : Equation20834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation20837_implies_Equation2 (G : Type*) [Magma G] (h : Equation20837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq148 eq57


@[equational_result]
theorem Equation20840_implies_Equation2 (G : Type*) [Magma G] (h : Equation20840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq34 eq13


@[equational_result]
theorem Equation20842_implies_Equation2 (G : Type*) [Magma G] (h : Equation20842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq56 eq19


@[equational_result]
theorem Equation20843_implies_Equation2 (G : Type*) [Magma G] (h : Equation20843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq9 eq9
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq26 eq18


@[equational_result]
theorem Equation20844_implies_Equation2 (G : Type*) [Magma G] (h : Equation20844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation20847_implies_Equation2 (G : Type*) [Magma G] (h : Equation20847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) ◇ X0) := superpose eq7 eq9
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq14
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq96 eq32


@[equational_result]
theorem Equation20850_implies_Equation2 (G : Type*) [Magma G] (h : Equation20850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ X0) := superpose eq7 eq12
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq14
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq147 eq51


@[equational_result]
theorem Equation20852_implies_Equation2 (G : Type*) [Magma G] (h : Equation20852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq35 eq14


@[equational_result]
theorem Equation20854_implies_Equation2 (G : Type*) [Magma G] (h : Equation20854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation20856_implies_Equation2 (G : Type*) [Magma G] (h : Equation20856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X1) = (((((X0 ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X2) ◇ X0) ◇ (X1 ◇ X1))) ◇ X0) := superpose eq7 eq10
  have eq21 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq16
  have eq23 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq21 eq17
  have eq44 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq23
  have eq101 (X0 X2 : G) : X0 = X2 := superpose eq7 eq44
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq101 eq8
  subsumption eq147 eq101


@[equational_result]
theorem Equation20858_implies_Equation2 (G : Type*) [Magma G] (h : Equation20858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq135 eq38


@[equational_result]
theorem Equation20860_implies_Equation2 (G : Type*) [Magma G] (h : Equation20860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq116 eq38


@[equational_result]
theorem Equation20862_implies_Equation2 (G : Type*) [Magma G] (h : Equation20862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation20865_implies_Equation2 (G : Type*) [Magma G] (h : Equation20865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X0 ◇ X3) ◇ X3) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X3) ◇ X3) ◇ X3))) := superpose eq7 eq9
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9
  have eq37 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq7 eq20
  have eq49 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = ((X2 ◇ X2) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) := superpose eq28 eq10
  have eq50 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) = X2 := superpose eq28 eq7
  have eq80 (X0 X1 X3 X4 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X3 ◇ X4) ◇ X4) ◇ X4)) = X3 := superpose eq37 eq7
  have eq88 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X3) ◇ X3)) = X3 := superpose eq37 eq7
  have eq176 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X3) ◇ X3)) = (((X1 ◇ X1) ◇ X3) ◇ X3) := superpose eq15 eq7
  have eq199 (X1 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ X3) = X3 := superpose eq88 eq176
  have eq202 (X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X1)) = X1 := superpose eq199 eq49
  have eq203 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X2 := superpose eq199 eq50
  have eq232 (X1 X3 X4 : G) : (X1 ◇ (((X3 ◇ X4) ◇ X4) ◇ X4)) = X3 := superpose eq202 eq80
  have eq278 (X3 : G) : (X3 ◇ X3) = X3 := superpose eq203 eq199
  have eq292 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq278 eq202
  have eq308 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq278 eq292
  have eq309 (X1 X3 X4 : G) : (X1 ◇ (X4 ◇ X4)) = X3 := superpose eq308 eq232
  have eq311 (X1 X3 X4 : G) : (X1 ◇ X4) = X3 := superpose eq278 eq309
  have eq320 (X0 X1 : G) : X0 = X1 := superpose eq278 eq311
  have eq360 (X0 : G) : sK0 ≠ X0 := superpose eq320 eq8
  subsumption eq360 eq320


@[equational_result]
theorem Equation20866_implies_Equation2 (G : Type*) [Magma G] (h : Equation20866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq153 eq54


@[equational_result]
theorem Equation20868_implies_Equation2 (G : Type*) [Magma G] (h : Equation20868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation20869_implies_Equation2 (G : Type*) [Magma G] (h : Equation20869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation20870_implies_Equation2 (G : Type*) [Magma G] (h : Equation20870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X0 ◇ X5) ◇ X5)) := superpose eq7 eq7
  have eq48 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq68 (X0 X2 : G) : X0 = X2 := superpose eq48 eq48
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq160 eq68


@[equational_result]
theorem Equation20871_implies_Equation2 (G : Type*) [Magma G] (h : Equation20871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation20874_implies_Equation2 (G : Type*) [Magma G] (h : Equation20874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X2) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq12
  have eq51 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X2) = X0 := superpose eq7 eq19
  have eq123 (X0 X3 : G) : X0 = X3 := superpose eq51 eq51
  have eq236 (X0 : G) : sK0 ≠ X0 := superpose eq123 eq8
  subsumption eq236 eq123


@[equational_result]
theorem Equation20877_implies_Equation2 (G : Type*) [Magma G] (h : Equation20877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X3) := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) ◇ X2) = X0 := superpose eq7 eq9
  have eq65 (X0 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ X2) := superpose eq23 eq22
  have eq152 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X3) = X0 := superpose eq7 eq65
  have eq286 (X0 X3 : G) : X0 = X3 := superpose eq7 eq152
  have eq475 (X0 : G) : sK0 ≠ X0 := superpose eq286 eq8
  subsumption eq475 eq286


@[equational_result]
theorem Equation20879_implies_Equation2 (G : Type*) [Magma G] (h : Equation20879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq36 eq15


@[equational_result]
theorem Equation20881_implies_Equation2 (G : Type*) [Magma G] (h : Equation20881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation20884_implies_Equation2 (G : Type*) [Magma G] (h : Equation20884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq10 eq12
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20886_implies_Equation2 (G : Type*) [Magma G] (h : Equation20886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation20887_implies_Equation2 (G : Type*) [Magma G] (h : Equation20887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation20889_implies_Equation2 (G : Type*) [Magma G] (h : Equation20889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation20890_implies_Equation2 (G : Type*) [Magma G] (h : Equation20890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation20891_implies_Equation2 (G : Type*) [Magma G] (h : Equation20891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20893_implies_Equation2 (G : Type*) [Magma G] (h : Equation20893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X2 := superpose eq9 eq9
  have eq33 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X3 ◇ X3) ◇ (X3 ◇ X3)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) := superpose eq10 eq9
  have eq49 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq9 eq33
  have eq52 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X2 := superpose eq49 eq31
  have eq73 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = X2 := superpose eq49 eq52
  have eq74 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq49 eq73
  have eq146 (X0 X1 : G) : X0 = X1 := superpose eq49 eq74
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq146 eq8
  subsumption eq151 eq146


@[equational_result]
theorem Equation20894_implies_Equation2 (G : Type*) [Magma G] (h : Equation20894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X1)) := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) = ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) := superpose eq10 eq10
  have eq23 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq7
  have eq35 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X2) ◇ (((X1 ◇ X4) ◇ X0) ◇ X4)))) = X3 := superpose eq7 eq9
  have eq44 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq9
  have eq53 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq10 eq44
  have eq54 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) = X1 := superpose eq44 eq9
  have eq56 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq44 eq7
  have eq64 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq54
  have eq69 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X2) ◇ (((X1 ◇ X4) ◇ X0) ◇ X4)))) = X3 := superpose eq64 eq35
  have eq70 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq56 eq53
  have eq81 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq70 eq44
  have eq98 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq81 eq10
  have eq99 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X1)) := superpose eq81 eq13
  have eq100 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq81 eq14
  have eq104 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq81 eq23
  have eq161 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq81 eq98
  have eq166 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq81 eq98
  have eq188 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq161 eq166
  have eq189 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq104 eq188
  have eq191 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) := superpose eq189 eq100
  have eq194 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X0 := superpose eq81 eq191
  have eq195 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq194 eq99
  have eq197 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq81 eq195
  have eq200 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X4)))) = X3 := superpose eq197 eq69
  have eq239 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X4))) = X3 := superpose eq197 eq200
  have eq240 (X0 X1 X3 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X3 := superpose eq197 eq239
  have eq241 (X1 X3 X4 : G) : (X1 ◇ X4) = X3 := superpose eq197 eq240
  have eq242 (X0 X1 : G) : X0 = X1 := superpose eq81 eq241
  have eq250 (X0 : G) : sK0 ≠ X0 := superpose eq242 eq8
  subsumption eq250 eq242


@[equational_result]
theorem Equation20895_implies_Equation2 (G : Type*) [Magma G] (h : Equation20895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq155 eq49


@[equational_result]
theorem Equation20897_implies_Equation2 (G : Type*) [Magma G] (h : Equation20897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20898_implies_Equation2 (G : Type*) [Magma G] (h : Equation20898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20899_implies_Equation2 (G : Type*) [Magma G] (h : Equation20899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20901_implies_Equation2 (G : Type*) [Magma G] (h : Equation20901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20902_implies_Equation2 (G : Type*) [Magma G] (h : Equation20902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20903_implies_Equation2 (G : Type*) [Magma G] (h : Equation20903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20905_implies_Equation2 (G : Type*) [Magma G] (h : Equation20905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20906_implies_Equation2 (G : Type*) [Magma G] (h : Equation20906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20907_implies_Equation2 (G : Type*) [Magma G] (h : Equation20907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20908_implies_Equation2 (G : Type*) [Magma G] (h : Equation20908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20910_implies_Equation2 (G : Type*) [Magma G] (h : Equation20910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ X2) = ((X1 ◇ X1) ◇ ((X0 ◇ (((X3 ◇ X0) ◇ X0) ◇ X2)) ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X0) ◇ (((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X3 ◇ X4) ◇ X4))))) ◇ X0) = X4 := superpose eq9 eq7
  have eq22 (X0 X2 X5 : G) : ((X5 ◇ X5) ◇ ((X2 ◇ X0) ◇ X5)) = X0 := superpose eq9 eq10
  have eq32 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))))) = X4 := superpose eq10 eq22
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X4) = ((X3 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3)) := superpose eq10 eq22
  have eq49 (X0 X1 X2 X4 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X4) = X2 := superpose eq22 eq36
  have eq56 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) = X4 := superpose eq49 eq32
  have eq59 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq56 eq16
  have eq146 (X0 X2 : G) : X0 = X2 := superpose eq59 eq59
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq146 eq8
  subsumption eq154 eq146


@[equational_result]
theorem Equation20912_implies_Equation2 (G : Type*) [Magma G] (h : Equation20912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq164 eq60


@[equational_result]
theorem Equation20914_implies_Equation2 (G : Type*) [Magma G] (h : Equation20914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X2) ◇ X2) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) = X0 := superpose eq7 eq9
  have eq26 (X0 X1 X2 X4 : G) : ((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2)) = X4 := superpose eq9 eq7
  have eq34 (X0 X2 X4 : G) : ((X2 ◇ X2) ◇ X0) = X4 := superpose eq22 eq26
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq7 eq34
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq130 eq53


@[equational_result]
theorem Equation20916_implies_Equation2 (G : Type*) [Magma G] (h : Equation20916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq61 eq15


@[equational_result]
theorem Equation20920_implies_Equation2 (G : Type*) [Magma G] (h : Equation20920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq179 eq57


@[equational_result]
theorem Equation20922_implies_Equation2 (G : Type*) [Magma G] (h : Equation20922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq83 eq19


@[equational_result]
theorem Equation20923_implies_Equation2 (G : Type*) [Magma G] (h : Equation20923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : ((X1 ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation20924_implies_Equation2 (G : Type*) [Magma G] (h : Equation20924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq64 eq14


@[equational_result]
theorem Equation20925_implies_Equation2 (G : Type*) [Magma G] (h : Equation20925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation20927_implies_Equation2 (G : Type*) [Magma G] (h : Equation20927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X0) ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) ◇ X2) = X0 := superpose eq7 eq10
  have eq22 (X0 X1 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq10 eq7
  have eq64 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X2) = X5 := superpose eq20 eq20
  have eq66 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((X3 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X1) := superpose eq10 eq20
  have eq93 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq64 eq66
  have eq98 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq93 eq22
  have eq137 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq93 eq98
  have eq138 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq93 eq137
  have eq258 (X0 X2 : G) : X0 = X2 := superpose eq138 eq138
  have eq260 (X0 : G) : sK0 ≠ X0 := superpose eq258 eq8
  subsumption eq260 eq258


@[equational_result]
theorem Equation20929_implies_Equation2 (G : Type*) [Magma G] (h : Equation20929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq72 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq169 eq72


@[equational_result]
theorem Equation20931_implies_Equation2 (G : Type*) [Magma G] (h : Equation20931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20932_implies_Equation2 (G : Type*) [Magma G] (h : Equation20932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20933_implies_Equation2 (G : Type*) [Magma G] (h : Equation20933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20935_implies_Equation2 (G : Type*) [Magma G] (h : Equation20935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20936_implies_Equation2 (G : Type*) [Magma G] (h : Equation20936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20937_implies_Equation2 (G : Type*) [Magma G] (h : Equation20937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20939_implies_Equation2 (G : Type*) [Magma G] (h : Equation20939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20940_implies_Equation2 (G : Type*) [Magma G] (h : Equation20940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20941_implies_Equation2 (G : Type*) [Magma G] (h : Equation20941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20942_implies_Equation2 (G : Type*) [Magma G] (h : Equation20942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20944_implies_Equation2 (G : Type*) [Magma G] (h : Equation20944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq44 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq10 eq11
  have eq47 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2)) = X3 := superpose eq11 eq7
  have eq70 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = X3 := superpose eq44 eq47
  have eq77 (X0 X3 : G) : X0 = X3 := superpose eq7 eq70
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq161 eq77


@[equational_result]
theorem Equation20945_implies_Equation2 (G : Type*) [Magma G] (h : Equation20945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X2 ◇ X2) ◇ X0) ◇ X2) ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) = X0 := superpose eq7 eq9
  have eq32 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (((X2 ◇ X2) ◇ X3) ◇ X2)) = X3 := superpose eq9 eq7
  have eq37 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq32 eq10
  have eq39 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq37 eq22
  have eq54 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq37 eq39
  have eq56 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq54 eq37
  have eq65 (X0 X1 : G) : X0 = X1 := superpose eq56 eq54
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq75 eq65


@[equational_result]
theorem Equation20946_implies_Equation2 (G : Type*) [Magma G] (h : Equation20946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation20948_implies_Equation2 (G : Type*) [Magma G] (h : Equation20948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20949_implies_Equation2 (G : Type*) [Magma G] (h : Equation20949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20950_implies_Equation2 (G : Type*) [Magma G] (h : Equation20950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20952_implies_Equation2 (G : Type*) [Magma G] (h : Equation20952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20953_implies_Equation2 (G : Type*) [Magma G] (h : Equation20953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20954_implies_Equation2 (G : Type*) [Magma G] (h : Equation20954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20956_implies_Equation2 (G : Type*) [Magma G] (h : Equation20956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20957_implies_Equation2 (G : Type*) [Magma G] (h : Equation20957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20958_implies_Equation2 (G : Type*) [Magma G] (h : Equation20958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20959_implies_Equation2 (G : Type*) [Magma G] (h : Equation20959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20961_implies_Equation2 (G : Type*) [Magma G] (h : Equation20961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ X0) ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4))) ◇ X0) := superpose eq7 eq7
  have eq44 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) = X0 := superpose eq10 eq11
  have eq69 (X0 X3 X4 : G) : (X3 ◇ X4) = (X4 ◇ X0) := superpose eq44 eq12
  have eq71 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq10 eq69
  have eq115 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X3) = X0 := superpose eq71 eq7
  have eq132 (X0 X3 : G) : X0 = X3 := superpose eq10 eq115
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq132 eq8
  subsumption eq163 eq132


@[equational_result]
theorem Equation20962_implies_Equation2 (G : Type*) [Magma G] (h : Equation20962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X5) ◇ (X2 ◇ X2))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq9 eq9
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq174 eq64


@[equational_result]
theorem Equation20963_implies_Equation2 (G : Type*) [Magma G] (h : Equation20963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ X0) ◇ X4) = ((X1 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4)) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = ((X3 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) := superpose eq10 eq7
  have eq38 (X2 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = X2 := superpose eq7 eq34
  have eq39 (X0 X3 X4 : G) : (((X3 ◇ X4) ◇ X0) ◇ X4) = X0 := superpose eq38 eq10
  have eq54 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq39 eq7
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = (X2 ◇ X0) := superpose eq39 eq11
  have eq59 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq54 eq55
  have eq60 (X2 X4 X5 : G) : (X4 ◇ X5) = X2 := superpose eq59 eq38
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq60 eq60
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq68 eq63


@[equational_result]
theorem Equation20964_implies_Equation2 (G : Type*) [Magma G] (h : Equation20964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation20966_implies_Equation2 (G : Type*) [Magma G] (h : Equation20966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20967_implies_Equation2 (G : Type*) [Magma G] (h : Equation20967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20968_implies_Equation2 (G : Type*) [Magma G] (h : Equation20968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20969_implies_Equation2 (G : Type*) [Magma G] (h : Equation20969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20971_implies_Equation2 (G : Type*) [Magma G] (h : Equation20971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20972_implies_Equation2 (G : Type*) [Magma G] (h : Equation20972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20973_implies_Equation2 (G : Type*) [Magma G] (h : Equation20973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20974_implies_Equation2 (G : Type*) [Magma G] (h : Equation20974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20976_implies_Equation2 (G : Type*) [Magma G] (h : Equation20976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20977_implies_Equation2 (G : Type*) [Magma G] (h : Equation20977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20978_implies_Equation2 (G : Type*) [Magma G] (h : Equation20978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20979_implies_Equation2 (G : Type*) [Magma G] (h : Equation20979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20981_implies_Equation2 (G : Type*) [Magma G] (h : Equation20981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20982_implies_Equation2 (G : Type*) [Magma G] (h : Equation20982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20983_implies_Equation2 (G : Type*) [Magma G] (h : Equation20983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20984_implies_Equation2 (G : Type*) [Magma G] (h : Equation20984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20985_implies_Equation2 (G : Type*) [Magma G] (h : Equation20985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation20987_implies_Equation2 (G : Type*) [Magma G] (h : Equation20987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ X3) ◇ X3) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq9 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq38 eq34


@[equational_result]
theorem Equation20988_implies_Equation2 (G : Type*) [Magma G] (h : Equation20988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq11
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq7 eq15
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq98 eq31


@[equational_result]
theorem Equation20989_implies_Equation2 (G : Type*) [Magma G] (h : Equation20989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation20991_implies_Equation2 (G : Type*) [Magma G] (h : Equation20991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ X3) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq9 eq11
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq36 eq30


@[equational_result]
theorem Equation20992_implies_Equation2 (G : Type*) [Magma G] (h : Equation20992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ X3) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq11
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (((X1 ◇ X1) ◇ X3) ◇ (((X0 ◇ X0) ◇ (X4 ◇ X5)) ◇ (((X3 ◇ X3) ◇ X4) ◇ X5))))) = X2 := superpose eq9 eq9
  have eq80 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq11 eq20
  have eq90 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X0) = X2 := superpose eq80 eq11
  have eq91 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) ◇ X1) = X2 := superpose eq80 eq20
  have eq120 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq80 eq91
  have eq122 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (((X1 ◇ X1) ◇ X3) ◇ (((X0 ◇ X0) ◇ (X4 ◇ X5)) ◇ X3)))) = X2 := superpose eq120 eq35
  have eq151 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq120 eq122
  have eq152 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq151 eq90
  have eq158 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq151 eq152
  have eq159 (X0 X3 : G) : X0 = X3 := superpose eq158 eq158
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq159 eq8
  subsumption eq161 eq159


@[equational_result]
theorem Equation20993_implies_Equation2 (G : Type*) [Magma G] (h : Equation20993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation20996_implies_Equation2 (G : Type*) [Magma G] (h : Equation20996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X3) = ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) = ((X4 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) ◇ (((X4 ◇ X4) ◇ X3) ◇ X3)) = X4 := superpose eq10 eq7
  have eq35 (X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) = X2 := superpose eq11 eq21
  have eq50 (X0 X1 X2 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq11
  have eq61 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq35 eq50
  have eq63 (X1 X3 X4 : G) : (X1 ◇ (((X4 ◇ X4) ◇ X3) ◇ X3)) = X4 := superpose eq61 eq29
  have eq71 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) = X3 := superpose eq63 eq9
  have eq78 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq63 eq71
  have eq104 (X0 X2 : G) : X0 = X2 := superpose eq78 eq78
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq104 eq8
  subsumption eq112 eq104


@[equational_result]
theorem Equation20997_implies_Equation2 (G : Type*) [Magma G] (h : Equation20997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation20999_implies_Equation2 (G : Type*) [Magma G] (h : Equation20999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation21000_implies_Equation2 (G : Type*) [Magma G] (h : Equation21000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq67 eq19


@[equational_result]
theorem Equation21001_implies_Equation2 (G : Type*) [Magma G] (h : Equation21001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ (((X4 ◇ X4) ◇ X5) ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X4) ◇ X4))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq9 eq11
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation21002_implies_Equation2 (G : Type*) [Magma G] (h : Equation21002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation21004_implies_Equation2 (G : Type*) [Magma G] (h : Equation21004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (((X0 ◇ (X3 ◇ X4)) ◇ X0) ◇ (X3 ◇ X4)))) = X2 := superpose eq9 eq9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq12
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq129 eq41


@[equational_result]
theorem Equation21006_implies_Equation2 (G : Type*) [Magma G] (h : Equation21006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation21008_implies_Equation2 (G : Type*) [Magma G] (h : Equation21008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (((X0 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4))) ◇ (((X0 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)))) = X2 := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq13
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq139 eq42


@[equational_result]
theorem Equation21009_implies_Equation2 (G : Type*) [Magma G] (h : Equation21009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X1 ◇ ((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) ◇ X3)) = ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq7
  have eq40 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq12
  have eq42 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq11 eq12
  have eq68 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq10
  have eq69 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq9 eq10
  have eq70 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) ◇ X0) := superpose eq11 eq10
  have eq86 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq69
  have eq87 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) ◇ X0) := superpose eq42 eq70
  have eq90 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1))) ◇ (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1))) = ((X2 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq11 eq40
  have eq131 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1))) ◇ (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1))) ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X0 := superpose eq11 eq68
  have eq164 (X0 X2 X3 : G) : (((((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X0 := superpose eq90 eq131
  have eq200 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq164 eq68
  have eq234 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := superpose eq87 eq7
  have eq258 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq7 eq234
  have eq271 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq258 eq10
  have eq355 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq16 eq11
  have eq444 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq258 eq355
  have eq448 (X0 X1 X2 : G) : (((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) ◇ X0) ◇ X1) = X2 := superpose eq7 eq355
  have eq648 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (((X2 ◇ X0) ◇ X0) ◇ X2))) ◇ X1) = X2 := superpose eq448 eq448
  have eq662 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) := superpose eq448 eq7
  have eq689 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq448 eq355
  have eq700 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq662 eq200
  have eq703 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq689 eq700
  have eq706 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) ◇ X1) = X2 := superpose eq689 eq648
  have eq792 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ (((X0 ◇ (X4 ◇ X5)) ◇ (X4 ◇ X5)) ◇ ((((((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ X4) ◇ X4) ◇ X5)))) = X1 := superpose eq9 eq86
  have eq818 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((((X0 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ X3) ◇ X3) ◇ X4)) ◇ X1) := superpose eq86 eq7
  have eq864 (X0 X1 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq703 eq86
  have eq912 (X0 X1 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0)) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq42 eq864
  have eq913 (X0 X1 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq706 eq912
  have eq914 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq706 eq913
  have eq918 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq914 eq444
  have eq927 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq918 eq258
  have eq932 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq918 eq271
  have eq959 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq927 eq918
  have eq962 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq927 eq959
  have eq996 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq962 eq932
  have eq997 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ X3) ◇ X3) ◇ X4)) ◇ X1) := superpose eq996 eq818
  have eq1004 (X0 X1 X4 X5 : G) : (X0 ◇ (X1 ◇ (((X0 ◇ (X4 ◇ X5)) ◇ (X4 ◇ X5)) ◇ (((X1 ◇ X4) ◇ X4) ◇ X5)))) = X1 := superpose eq997 eq792
  have eq1050 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq9 eq1004
  have eq1652 (X0 X2 : G) : X0 = X2 := superpose eq1050 eq1050
  have eq1654 (X0 : G) : sK0 ≠ X0 := superpose eq1652 eq8
  subsumption eq1654 eq1652


@[equational_result]
theorem Equation21010_implies_Equation2 (G : Type*) [Magma G] (h : Equation21010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation21014_implies_Equation2 (G : Type*) [Magma G] (h : Equation21014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq55 eq16


@[equational_result]
theorem Equation21016_implies_Equation2 (G : Type*) [Magma G] (h : Equation21016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation21017_implies_Equation2 (G : Type*) [Magma G] (h : Equation21017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation21018_implies_Equation2 (G : Type*) [Magma G] (h : Equation21018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation21019_implies_Equation2 (G : Type*) [Magma G] (h : Equation21019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation21022_implies_Equation2 (G : Type*) [Magma G] (h : Equation21022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq12
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq123 eq59


@[equational_result]
theorem Equation21023_implies_Equation2 (G : Type*) [Magma G] (h : Equation21023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation21027_implies_Equation2 (G : Type*) [Magma G] (h : Equation21027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation21030_implies_Equation2 (G : Type*) [Magma G] (h : Equation21030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (((X3 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X2) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ ((X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X2) ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3))) ◇ ((X0 ◇ (((X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3))) ◇ (((X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)))) = X2 := superpose eq9 eq7
  have eq42 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ (((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3))) ◇ ((X1 ◇ (((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3))) ◇ (((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3))))) = X4 := superpose eq10 eq9
  have eq51 (X2 X4 : G) : (X2 ◇ X2) = X4 := superpose eq15 eq42
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq7 eq51
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq143 eq53


@[equational_result]
theorem Equation21031_implies_Equation2 (G : Type*) [Magma G] (h : Equation21031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation21033_implies_Equation2 (G : Type*) [Magma G] (h : Equation21033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation21034_implies_Equation2 (G : Type*) [Magma G] (h : Equation21034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation21035_implies_Equation2 (G : Type*) [Magma G] (h : Equation21035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X0 ◇ X2) ◇ X4) ◇ X4))) = X3 := superpose eq7 eq7
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq59 eq24


@[equational_result]
theorem Equation21036_implies_Equation2 (G : Type*) [Magma G] (h : Equation21036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation21038_implies_Equation2 (G : Type*) [Magma G] (h : Equation21038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ X4) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq118 eq41


@[equational_result]
theorem Equation21039_implies_Equation2 (G : Type*) [Magma G] (h : Equation21039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq12
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq160 eq59


@[equational_result]
theorem Equation21040_implies_Equation2 (G : Type*) [Magma G] (h : Equation21040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation21041_implies_Equation2 (G : Type*) [Magma G] (h : Equation21041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation21043_implies_Equation2 (G : Type*) [Magma G] (h : Equation21043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq154 eq65


@[equational_result]
theorem Equation21044_implies_Equation2 (G : Type*) [Magma G] (h : Equation21044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq153 eq67


@[equational_result]
theorem Equation21045_implies_Equation2 (G : Type*) [Magma G] (h : Equation21045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X2)) ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ (X0 ◇ X4)) = X2 := superpose eq7 eq7
  have eq38 (X0 X5 : G) : X0 = X5 := superpose eq9 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq48 eq38


@[equational_result]
theorem Equation21046_implies_Equation2 (G : Type*) [Magma G] (h : Equation21046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation21048_implies_Equation2 (G : Type*) [Magma G] (h : Equation21048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq154 eq67


@[equational_result]
theorem Equation21049_implies_Equation2 (G : Type*) [Magma G] (h : Equation21049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) ◇ (X0 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3))) = X4 := superpose eq7 eq7
  have eq54 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq73 eq54


@[equational_result]
theorem Equation21050_implies_Equation2 (G : Type*) [Magma G] (h : Equation21050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq71 eq16


@[equational_result]
theorem Equation21051_implies_Equation2 (G : Type*) [Magma G] (h : Equation21051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation21053_implies_Equation2 (G : Type*) [Magma G] (h : Equation21053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation21054_implies_Equation2 (G : Type*) [Magma G] (h : Equation21054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) ◇ X0) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation21055_implies_Equation2 (G : Type*) [Magma G] (h : Equation21055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ X5) ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X0 ◇ X4) ◇ X4) ◇ X4))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq9 eq11
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq60 eq18


@[equational_result]
theorem Equation21056_implies_Equation2 (G : Type*) [Magma G] (h : Equation21056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation21058_implies_Equation2 (G : Type*) [Magma G] (h : Equation21058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation21059_implies_Equation2 (G : Type*) [Magma G] (h : Equation21059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation21060_implies_Equation2 (G : Type*) [Magma G] (h : Equation21060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation21061_implies_Equation2 (G : Type*) [Magma G] (h : Equation21061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ (((X5 ◇ X6) ◇ X7) ◇ X7)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X0 ◇ X5) ◇ X6) ◇ X6))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq9 eq11
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation21062_implies_Equation2 (G : Type*) [Magma G] (h : Equation21062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation21064_implies_Equation2 (G : Type*) [Magma G] (h : Equation21064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq9 eq9
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq139 eq63


@[equational_result]
theorem Equation21065_implies_Equation2 (G : Type*) [Magma G] (h : Equation21065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X3) ◇ X3) ◇ X2)) ◇ X3) = X2 := superpose eq11 eq11
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0)) ◇ X3) ◇ ((X0 ◇ X2) ◇ X3)) = X2 := superpose eq11 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0)) ◇ X3) ◇ X3) ◇ X2)) = X3 := superpose eq11 eq7
  have eq42 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X2)) = X2 := superpose eq11 eq16
  have eq84 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X0) := superpose eq11 eq10
  have eq105 (X0 X1 X2 : G) : ((X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0)) ◇ (X0 ◇ X2)) = X2 := superpose eq11 eq42
  have eq109 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq42 eq42
  have eq139 (X0 X1 : G) : ((X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose eq84 eq11
  have eq140 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ ((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X1)) = X2 := superpose eq84 eq7
  have eq269 (X0 X1 : G) : (((X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ X0) = ((((X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ X0) := superpose eq17 eq109
  have eq297 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq269
  have eq368 (X0 X1 X2 : G) : (((X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq297 eq13
  have eq371 (X0 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq297 eq139
  have eq401 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq297 eq371
  have eq402 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq42 eq401
  have eq404 (X0 X1 X2 : G) : (((X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0)) ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq402 eq368
  have eq409 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq105 eq404
  have eq413 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X1)) = X2 := superpose eq409 eq140
  have eq724 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2)) = X2 := superpose eq409 eq413
  have eq725 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X2 := superpose eq409 eq724
  have eq726 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq409 eq725
  have eq727 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq409 eq726
  have eq728 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq409 eq727
  have eq729 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X2 := superpose eq409 eq728
  have eq730 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq409 eq729
  have eq731 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq409 eq730
  have eq747 (X0 X2 : G) : X0 = X2 := superpose eq731 eq731
  have eq749 (X0 : G) : sK0 ≠ X0 := superpose eq747 eq8
  subsumption eq749 eq747


@[equational_result]
theorem Equation21066_implies_Equation2 (G : Type*) [Magma G] (h : Equation21066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation21068_implies_Equation2 (G : Type*) [Magma G] (h : Equation21068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)))) = X4 := superpose eq9 eq9
  have eq21 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq9 eq13
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq146 eq42


@[equational_result]
theorem Equation21070_implies_Equation2 (G : Type*) [Magma G] (h : Equation21070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation21074_implies_Equation2 (G : Type*) [Magma G] (h : Equation21074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq55 eq16


@[equational_result]
theorem Equation21076_implies_Equation2 (G : Type*) [Magma G] (h : Equation21076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation21077_implies_Equation2 (G : Type*) [Magma G] (h : Equation21077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation21078_implies_Equation2 (G : Type*) [Magma G] (h : Equation21078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation21079_implies_Equation2 (G : Type*) [Magma G] (h : Equation21079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation21081_implies_Equation2 (G : Type*) [Magma G] (h : Equation21081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq26 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ ((((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X3)))) = X4 := superpose eq9 eq9
  have eq48 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq9 eq26
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq7 eq48
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq109 eq49


@[equational_result]
theorem Equation21082_implies_Equation2 (G : Type*) [Magma G] (h : Equation21082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0)) ◇ (X1 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0))) ◇ X3) ◇ X2)) = X3 := superpose eq11 eq7
  have eq46 (X0 X1 X2 X3 : G) : (X0 ◇ (((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X3) ◇ X2)) = X3 := superpose eq10 eq41
  have eq58 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X4) ◇ ((((X2 ◇ ((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) ◇ X0)) ◇ (X2 ◇ ((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) ◇ X0))) ◇ X1) ◇ X3))) = X4 := superpose eq11 eq9
  have eq87 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X4) ◇ (((((X2 ◇ X2) ◇ X2) ◇ X2) ◇ X1) ◇ X3))) = X4 := superpose eq10 eq58
  have eq88 (X1 X4 : G) : (X1 ◇ X1) = X4 := superpose eq46 eq87
  have eq96 (X0 X2 : G) : X0 = X2 := superpose eq88 eq88
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq191 eq96


@[equational_result]
theorem Equation21083_implies_Equation2 (G : Type*) [Magma G] (h : Equation21083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation21085_implies_Equation2 (G : Type*) [Magma G] (h : Equation21085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation21086_implies_Equation2 (G : Type*) [Magma G] (h : Equation21086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21087_implies_Equation2 (G : Type*) [Magma G] (h : Equation21087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21089_implies_Equation2 (G : Type*) [Magma G] (h : Equation21089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21090_implies_Equation2 (G : Type*) [Magma G] (h : Equation21090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21091_implies_Equation2 (G : Type*) [Magma G] (h : Equation21091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21093_implies_Equation2 (G : Type*) [Magma G] (h : Equation21093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21094_implies_Equation2 (G : Type*) [Magma G] (h : Equation21094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21095_implies_Equation2 (G : Type*) [Magma G] (h : Equation21095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21096_implies_Equation2 (G : Type*) [Magma G] (h : Equation21096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21098_implies_Equation2 (G : Type*) [Magma G] (h : Equation21098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq9 eq14
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq60 eq22


@[equational_result]
theorem Equation21099_implies_Equation2 (G : Type*) [Magma G] (h : Equation21099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq12 eq12
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq13
  have eq67 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq31
  have eq124 (X0 X3 : G) : X0 = X3 := superpose eq12 eq67
  have eq229 (X0 : G) : sK0 ≠ X0 := superpose eq124 eq8
  subsumption eq229 eq124


@[equational_result]
theorem Equation21100_implies_Equation2 (G : Type*) [Magma G] (h : Equation21100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq41 eq15


@[equational_result]
theorem Equation21102_implies_Equation2 (G : Type*) [Magma G] (h : Equation21102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation21103_implies_Equation2 (G : Type*) [Magma G] (h : Equation21103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation21104_implies_Equation2 (G : Type*) [Magma G] (h : Equation21104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation21106_implies_Equation2 (G : Type*) [Magma G] (h : Equation21106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation21107_implies_Equation2 (G : Type*) [Magma G] (h : Equation21107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation21108_implies_Equation2 (G : Type*) [Magma G] (h : Equation21108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation21110_implies_Equation2 (G : Type*) [Magma G] (h : Equation21110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation21111_implies_Equation2 (G : Type*) [Magma G] (h : Equation21111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation21112_implies_Equation2 (G : Type*) [Magma G] (h : Equation21112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation21113_implies_Equation2 (G : Type*) [Magma G] (h : Equation21113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21115_implies_Equation2 (G : Type*) [Magma G] (h : Equation21115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X4) ◇ X5) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq9 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq142 eq41


@[equational_result]
theorem Equation21116_implies_Equation2 (G : Type*) [Magma G] (h : Equation21116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X5) ◇ X3)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X4) ◇ X0) ◇ X3) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq33 (X0 X1 X3 X5 : G) : ((X1 ◇ X5) ◇ (X3 ◇ X5)) = X0 := superpose eq10 eq11
  have eq85 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq173 eq85


@[equational_result]
theorem Equation21117_implies_Equation2 (G : Type*) [Magma G] (h : Equation21117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X4) ◇ X5) ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X5) ◇ (((X1 ◇ X4) ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X5 X6 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X6) ◇ X5)) = X6 := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X5 := superpose eq12 eq10
  have eq33 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq57 eq33


@[equational_result]
theorem Equation21118_implies_Equation2 (G : Type*) [Magma G] (h : Equation21118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation21120_implies_Equation2 (G : Type*) [Magma G] (h : Equation21120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21121_implies_Equation2 (G : Type*) [Magma G] (h : Equation21121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21122_implies_Equation2 (G : Type*) [Magma G] (h : Equation21122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21123_implies_Equation2 (G : Type*) [Magma G] (h : Equation21123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21125_implies_Equation2 (G : Type*) [Magma G] (h : Equation21125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21126_implies_Equation2 (G : Type*) [Magma G] (h : Equation21126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21127_implies_Equation2 (G : Type*) [Magma G] (h : Equation21127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21128_implies_Equation2 (G : Type*) [Magma G] (h : Equation21128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21130_implies_Equation2 (G : Type*) [Magma G] (h : Equation21130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21131_implies_Equation2 (G : Type*) [Magma G] (h : Equation21131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21132_implies_Equation2 (G : Type*) [Magma G] (h : Equation21132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21133_implies_Equation2 (G : Type*) [Magma G] (h : Equation21133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21135_implies_Equation2 (G : Type*) [Magma G] (h : Equation21135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21136_implies_Equation2 (G : Type*) [Magma G] (h : Equation21136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21137_implies_Equation2 (G : Type*) [Magma G] (h : Equation21137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21138_implies_Equation2 (G : Type*) [Magma G] (h : Equation21138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21139_implies_Equation2 (G : Type*) [Magma G] (h : Equation21139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21142_implies_Equation2 (G : Type*) [Magma G] (h : Equation21142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq11
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq7 eq16
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq101 eq35


@[equational_result]
theorem Equation21143_implies_Equation2 (G : Type*) [Magma G] (h : Equation21143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation21147_implies_Equation2 (G : Type*) [Magma G] (h : Equation21147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation21150_implies_Equation2 (G : Type*) [Magma G] (h : Equation21150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ X3) ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq11
  have eq24 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) = ((X3 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1))) := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = ((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) ◇ (X0 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)))) := superpose eq11 eq10
  have eq39 (X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) = X1 := superpose eq11 eq24
  have eq40 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq39 eq17
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = ((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq40 eq25
  have eq42 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq39 eq41
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) = X2 := superpose eq42 eq11
  have eq52 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq43 eq9
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq7 eq52
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq106 eq53


@[equational_result]
theorem Equation21151_implies_Equation2 (G : Type*) [Magma G] (h : Equation21151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation21153_implies_Equation2 (G : Type*) [Magma G] (h : Equation21153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation21154_implies_Equation2 (G : Type*) [Magma G] (h : Equation21154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation21155_implies_Equation2 (G : Type*) [Magma G] (h : Equation21155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X4) ◇ X5) ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X3 ◇ X0) ◇ X4) ◇ X4))) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ (((X5 ◇ X4) ◇ X6) ◇ X6))) = X5 := superpose eq7 eq11
  have eq29 (X0 X1 X3 X4 X5 X6 : G) : (X1 ◇ ((((X0 ◇ (X3 ◇ (((X0 ◇ X3) ◇ X4) ◇ X4))) ◇ X5) ◇ X6) ◇ X6)) = X5 := superpose eq11 eq9
  have eq46 (X0 X1 X5 X6 : G) : (X1 ◇ (((X0 ◇ X5) ◇ X6) ◇ X6)) = X5 := superpose eq12 eq29
  have eq49 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq46 eq12
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq49
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq147 eq51


@[equational_result]
theorem Equation21156_implies_Equation2 (G : Type*) [Magma G] (h : Equation21156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation21158_implies_Equation2 (G : Type*) [Magma G] (h : Equation21158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((((X2 ◇ X1) ◇ X0) ◇ X1) ◇ X1)) = (X0 ◇ X2) := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = (X0 ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq7 eq11
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X2) = X0 := superpose eq7 eq11
  have eq22 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X2)) = X1 := superpose eq11 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq11 eq7
  have eq30 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1)))) = X3 := superpose eq15 eq10
  have eq94 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ ((X1 ◇ X3) ◇ X0))) ◇ X2) := superpose eq21 eq11
  have eq174 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq23 eq23
  have eq242 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((((X2 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2)) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq12 eq30
  have eq268 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((((X2 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ (X3 ◇ X2)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2)) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq11 eq242
  have eq358 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ (((((X2 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq23 eq22
  have eq438 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq23 eq174
  have eq484 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((X2 ◇ (X3 ◇ X2)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2)) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq438 eq268
  have eq513 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X2 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2)) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq438 eq484
  have eq514 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq438 eq513
  have eq520 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X2) := superpose eq514 eq94
  have eq625 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X0)) = X0 := superpose eq520 eq7
  have eq707 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq625 eq21
  have eq712 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((((X2 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq707 eq358
  have eq738 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((((X2 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0)) = X3 := superpose eq707 eq712
  have eq739 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) = X3 := superpose eq707 eq738
  have eq740 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X0 ◇ X2))) = X3 := superpose eq707 eq739
  have eq741 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X1)) = X3 := superpose eq707 eq740
  have eq742 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = X3 := superpose eq707 eq741
  have eq743 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq707 eq742
  have eq744 (X0 X3 : G) : X0 = X3 := superpose eq743 eq743
  have eq749 (X0 : G) : sK0 ≠ X0 := superpose eq744 eq8
  subsumption eq749 eq744


@[equational_result]
theorem Equation21160_implies_Equation2 (G : Type*) [Magma G] (h : Equation21160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation21162_implies_Equation2 (G : Type*) [Magma G] (h : Equation21162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21163_implies_Equation2 (G : Type*) [Magma G] (h : Equation21163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21164_implies_Equation2 (G : Type*) [Magma G] (h : Equation21164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21166_implies_Equation2 (G : Type*) [Magma G] (h : Equation21166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21167_implies_Equation2 (G : Type*) [Magma G] (h : Equation21167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21168_implies_Equation2 (G : Type*) [Magma G] (h : Equation21168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21170_implies_Equation2 (G : Type*) [Magma G] (h : Equation21170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21171_implies_Equation2 (G : Type*) [Magma G] (h : Equation21171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21172_implies_Equation2 (G : Type*) [Magma G] (h : Equation21172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21173_implies_Equation2 (G : Type*) [Magma G] (h : Equation21173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21176_implies_Equation2 (G : Type*) [Magma G] (h : Equation21176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq12
  have eq58 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq122 eq58


@[equational_result]
theorem Equation21177_implies_Equation2 (G : Type*) [Magma G] (h : Equation21177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation21179_implies_Equation2 (G : Type*) [Magma G] (h : Equation21179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21180_implies_Equation2 (G : Type*) [Magma G] (h : Equation21180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21181_implies_Equation2 (G : Type*) [Magma G] (h : Equation21181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21183_implies_Equation2 (G : Type*) [Magma G] (h : Equation21183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21184_implies_Equation2 (G : Type*) [Magma G] (h : Equation21184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21185_implies_Equation2 (G : Type*) [Magma G] (h : Equation21185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21187_implies_Equation2 (G : Type*) [Magma G] (h : Equation21187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21188_implies_Equation2 (G : Type*) [Magma G] (h : Equation21188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21189_implies_Equation2 (G : Type*) [Magma G] (h : Equation21189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21190_implies_Equation2 (G : Type*) [Magma G] (h : Equation21190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21192_implies_Equation2 (G : Type*) [Magma G] (h : Equation21192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ X0) ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq10
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (((X3 ◇ X4) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X3 ◇ X5)) = X0 := superpose eq7 eq11
  have eq69 (X0 X3 X5 : G) : (X0 ◇ (X3 ◇ X5)) = X0 := superpose eq15 eq33
  have eq91 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq69
  have eq109 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := superpose eq91 eq7
  have eq132 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = X0 := superpose eq91 eq109
  have eq133 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq91 eq132
  have eq134 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq91 eq133
  have eq135 (X0 X3 : G) : X0 = X3 := superpose eq134 eq134
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq135 eq8
  subsumption eq137 eq135


@[equational_result]
theorem Equation21193_implies_Equation2 (G : Type*) [Magma G] (h : Equation21193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq12
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq146 eq45


@[equational_result]
theorem Equation21194_implies_Equation2 (G : Type*) [Magma G] (h : Equation21194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation21195_implies_Equation2 (G : Type*) [Magma G] (h : Equation21195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation21197_implies_Equation2 (G : Type*) [Magma G] (h : Equation21197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21198_implies_Equation2 (G : Type*) [Magma G] (h : Equation21198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21199_implies_Equation2 (G : Type*) [Magma G] (h : Equation21199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21200_implies_Equation2 (G : Type*) [Magma G] (h : Equation21200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21202_implies_Equation2 (G : Type*) [Magma G] (h : Equation21202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21203_implies_Equation2 (G : Type*) [Magma G] (h : Equation21203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21204_implies_Equation2 (G : Type*) [Magma G] (h : Equation21204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21205_implies_Equation2 (G : Type*) [Magma G] (h : Equation21205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21207_implies_Equation2 (G : Type*) [Magma G] (h : Equation21207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21208_implies_Equation2 (G : Type*) [Magma G] (h : Equation21208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21209_implies_Equation2 (G : Type*) [Magma G] (h : Equation21209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21210_implies_Equation2 (G : Type*) [Magma G] (h : Equation21210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21212_implies_Equation2 (G : Type*) [Magma G] (h : Equation21212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21213_implies_Equation2 (G : Type*) [Magma G] (h : Equation21213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21214_implies_Equation2 (G : Type*) [Magma G] (h : Equation21214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21215_implies_Equation2 (G : Type*) [Magma G] (h : Equation21215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21216_implies_Equation2 (G : Type*) [Magma G] (h : Equation21216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21218_implies_Equation2 (G : Type*) [Magma G] (h : Equation21218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ X5) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq163 eq71


@[equational_result]
theorem Equation21219_implies_Equation2 (G : Type*) [Magma G] (h : Equation21219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq11
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq109 eq39


@[equational_result]
theorem Equation21220_implies_Equation2 (G : Type*) [Magma G] (h : Equation21220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation21221_implies_Equation2 (G : Type*) [Magma G] (h : Equation21221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation21223_implies_Equation2 (G : Type*) [Magma G] (h : Equation21223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X4 ◇ X0) ◇ X2) ◇ X2))) = X3 := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X0)) = X3 := superpose eq7 eq9
  have eq25 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq17 eq15
  have eq75 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq170 eq75


@[equational_result]
theorem Equation21224_implies_Equation2 (G : Type*) [Magma G] (h : Equation21224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X4) ◇ (X0 ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X4)) ◇ X1)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X4))) = X4 := superpose eq11 eq11
  have eq21 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ (((X6 ◇ X0) ◇ X2) ◇ X3)) ◇ X0) = X5 := superpose eq7 eq11
  have eq44 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ (X5 ◇ X0)) ◇ X2))) ◇ X6) ◇ X7) ◇ X4) ◇ X0) = X7 := superpose eq12 eq11
  have eq49 (X0 X2 X4 X6 X7 : G) : ((((X2 ◇ X6) ◇ X7) ◇ X4) ◇ X0) = X7 := superpose eq19 eq44
  have eq54 (X0 X4 X5 : G) : (X4 ◇ X0) = X5 := superpose eq49 eq21
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq54
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq118 eq56


@[equational_result]
theorem Equation21225_implies_Equation2 (G : Type*) [Magma G] (h : Equation21225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X2)) ◇ X4)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X3) ◇ (X0 ◇ X2)) = X4 := superpose eq7 eq7
  have eq41 (X0 X6 : G) : X0 = X6 := superpose eq9 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq61 eq41


@[equational_result]
theorem Equation21226_implies_Equation2 (G : Type*) [Magma G] (h : Equation21226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation21228_implies_Equation2 (G : Type*) [Magma G] (h : Equation21228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X4)) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X0) ◇ X6)))) = X5 := superpose eq11 eq11
  have eq26 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (((X5 ◇ X6) ◇ (X3 ◇ X1)) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)))) = X6 := superpose eq11 eq7
  have eq32 (X0 X2 X3 X5 X6 : G) : (((X0 ◇ (X5 ◇ X6)) ◇ X2) ◇ X3) = X6 := superpose eq12 eq12
  have eq50 (X0 X1 X4 X5 : G) : (X0 ◇ (X4 ◇ (X1 ◇ X5))) = X5 := superpose eq32 eq20
  have eq52 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq50 eq26
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq52
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq172 eq53


@[equational_result]
theorem Equation21229_implies_Equation2 (G : Type*) [Magma G] (h : Equation21229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((X5 ◇ X0) ◇ X4) ◇ X4) = ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3))) = X3 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) = ((X5 ◇ (((X6 ◇ X0) ◇ X3) ◇ X3)) ◇ (X0 ◇ (((X6 ◇ X0) ◇ X3) ◇ X3))) := superpose eq7 eq10
  have eq30 (X0 X1 X2 X3 X4 X6 : G) : ((X3 ◇ X4) ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ X4)) = X6 := superpose eq10 eq7
  have eq36 (X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) = X3 := superpose eq11 eq22
  have eq40 (X1 X3 X4 X6 : G) : ((X3 ◇ X4) ◇ X1) = X6 := superpose eq36 eq30
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq40
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq158 eq68


@[equational_result]
theorem Equation21230_implies_Equation2 (G : Type*) [Magma G] (h : Equation21230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation21231_implies_Equation2 (G : Type*) [Magma G] (h : Equation21231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation21233_implies_Equation2 (G : Type*) [Magma G] (h : Equation21233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ X4) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) = X3 := superpose eq7 eq7
  have eq36 (X0 X6 : G) : X0 = X6 := superpose eq9 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation21234_implies_Equation2 (G : Type*) [Magma G] (h : Equation21234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation21235_implies_Equation2 (G : Type*) [Magma G] (h : Equation21235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ X4) ◇ X4)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X3 ◇ X0) ◇ X3) ◇ X3))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq9 eq11
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation21236_implies_Equation2 (G : Type*) [Magma G] (h : Equation21236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation21238_implies_Equation2 (G : Type*) [Magma G] (h : Equation21238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation21239_implies_Equation2 (G : Type*) [Magma G] (h : Equation21239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation21240_implies_Equation2 (G : Type*) [Magma G] (h : Equation21240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation21241_implies_Equation2 (G : Type*) [Magma G] (h : Equation21241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ (((X5 ◇ X6) ◇ X7) ◇ X7)) = X6 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (((X5 ◇ X0) ◇ X6) ◇ X6))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq9 eq11
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation21242_implies_Equation2 (G : Type*) [Magma G] (h : Equation21242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation21244_implies_Equation2 (G : Type*) [Magma G] (h : Equation21244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X4 ◇ (X1 ◇ X2)) ◇ X5) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (((X4 ◇ X2) ◇ X0) ◇ X2))) = X5 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X6 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X6) ◇ X0)) = X6 := superpose eq7 eq9
  have eq23 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq16 eq12
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq139 eq63


@[equational_result]
theorem Equation21245_implies_Equation2 (G : Type*) [Magma G] (h : Equation21245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ X3) ◇ X0) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) = ((X5 ◇ (((X6 ◇ X3) ◇ X0) ◇ X4)) ◇ X0) := superpose eq7 eq11
  have eq31 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3)) = X0 := superpose eq11 eq7
  have eq44 (X0 X1 X2 X6 X7 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X6) ◇ X7)) ◇ X6) = X7 := superpose eq12 eq12
  have eq70 (X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) = X4 := superpose eq44 eq25
  have eq72 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X0 := superpose eq70 eq31
  have eq80 (X0 X4 : G) : X0 = X4 := superpose eq7 eq72
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq182 eq80


@[equational_result]
theorem Equation21246_implies_Equation2 (G : Type*) [Magma G] (h : Equation21246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X4 ◇ (X1 ◇ X2)) ◇ X5) ◇ X4)) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X7 : G) : (X1 ◇ X0) = X7 := superpose eq9 eq9
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq170 eq65


@[equational_result]
theorem Equation21247_implies_Equation2 (G : Type*) [Magma G] (h : Equation21247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation21249_implies_Equation2 (G : Type*) [Magma G] (h : Equation21249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21250_implies_Equation2 (G : Type*) [Magma G] (h : Equation21250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21251_implies_Equation2 (G : Type*) [Magma G] (h : Equation21251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21252_implies_Equation2 (G : Type*) [Magma G] (h : Equation21252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21254_implies_Equation2 (G : Type*) [Magma G] (h : Equation21254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21255_implies_Equation2 (G : Type*) [Magma G] (h : Equation21255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21256_implies_Equation2 (G : Type*) [Magma G] (h : Equation21256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21257_implies_Equation2 (G : Type*) [Magma G] (h : Equation21257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21259_implies_Equation2 (G : Type*) [Magma G] (h : Equation21259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21260_implies_Equation2 (G : Type*) [Magma G] (h : Equation21260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21261_implies_Equation2 (G : Type*) [Magma G] (h : Equation21261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21262_implies_Equation2 (G : Type*) [Magma G] (h : Equation21262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21264_implies_Equation2 (G : Type*) [Magma G] (h : Equation21264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21265_implies_Equation2 (G : Type*) [Magma G] (h : Equation21265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21266_implies_Equation2 (G : Type*) [Magma G] (h : Equation21266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21267_implies_Equation2 (G : Type*) [Magma G] (h : Equation21267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21268_implies_Equation2 (G : Type*) [Magma G] (h : Equation21268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X1) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21270_implies_Equation2 (G : Type*) [Magma G] (h : Equation21270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X4 ◇ (((X3 ◇ X2) ◇ X0) ◇ X1)) ◇ X5) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) ◇ X5) ◇ X6) = (X0 ◇ (X5 ◇ (X4 ◇ X3))) := superpose eq7 eq11
  have eq32 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq11 eq7
  have eq41 (X0 X1 X2 X5 : G) : (X0 ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = X5 := superpose eq22 eq9
  have eq53 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq41 eq41
  have eq72 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq53 eq32
  have eq103 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X0) = X2 := superpose eq53 eq72
  have eq104 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq53 eq103
  have eq105 (X0 X3 : G) : X0 = X3 := superpose eq104 eq104
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq110 eq105


@[equational_result]
theorem Equation21271_implies_Equation2 (G : Type*) [Magma G] (h : Equation21271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq12
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq148 eq67


@[equational_result]
theorem Equation21272_implies_Equation2 (G : Type*) [Magma G] (h : Equation21272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation21273_implies_Equation2 (G : Type*) [Magma G] (h : Equation21273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation21275_implies_Equation2 (G : Type*) [Magma G] (h : Equation21275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21276_implies_Equation2 (G : Type*) [Magma G] (h : Equation21276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21277_implies_Equation2 (G : Type*) [Magma G] (h : Equation21277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21278_implies_Equation2 (G : Type*) [Magma G] (h : Equation21278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21280_implies_Equation2 (G : Type*) [Magma G] (h : Equation21280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21281_implies_Equation2 (G : Type*) [Magma G] (h : Equation21281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21282_implies_Equation2 (G : Type*) [Magma G] (h : Equation21282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21283_implies_Equation2 (G : Type*) [Magma G] (h : Equation21283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21285_implies_Equation2 (G : Type*) [Magma G] (h : Equation21285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21286_implies_Equation2 (G : Type*) [Magma G] (h : Equation21286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21287_implies_Equation2 (G : Type*) [Magma G] (h : Equation21287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21288_implies_Equation2 (G : Type*) [Magma G] (h : Equation21288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21290_implies_Equation2 (G : Type*) [Magma G] (h : Equation21290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21291_implies_Equation2 (G : Type*) [Magma G] (h : Equation21291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21292_implies_Equation2 (G : Type*) [Magma G] (h : Equation21292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21293_implies_Equation2 (G : Type*) [Magma G] (h : Equation21293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21294_implies_Equation2 (G : Type*) [Magma G] (h : Equation21294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X2) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21296_implies_Equation2 (G : Type*) [Magma G] (h : Equation21296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X4 ◇ X4) ◇ X5) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq32 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq32
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq147 eq42


@[equational_result]
theorem Equation21297_implies_Equation2 (G : Type*) [Magma G] (h : Equation21297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq31 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq12
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq140 eq40


@[equational_result]
theorem Equation21298_implies_Equation2 (G : Type*) [Magma G] (h : Equation21298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X4) ◇ (((X3 ◇ X3) ◇ X0) ◇ X3))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq10
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation21299_implies_Equation2 (G : Type*) [Magma G] (h : Equation21299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation21301_implies_Equation2 (G : Type*) [Magma G] (h : Equation21301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21302_implies_Equation2 (G : Type*) [Magma G] (h : Equation21302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21303_implies_Equation2 (G : Type*) [Magma G] (h : Equation21303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21304_implies_Equation2 (G : Type*) [Magma G] (h : Equation21304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21306_implies_Equation2 (G : Type*) [Magma G] (h : Equation21306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21307_implies_Equation2 (G : Type*) [Magma G] (h : Equation21307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21308_implies_Equation2 (G : Type*) [Magma G] (h : Equation21308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21309_implies_Equation2 (G : Type*) [Magma G] (h : Equation21309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21311_implies_Equation2 (G : Type*) [Magma G] (h : Equation21311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21312_implies_Equation2 (G : Type*) [Magma G] (h : Equation21312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21313_implies_Equation2 (G : Type*) [Magma G] (h : Equation21313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21314_implies_Equation2 (G : Type*) [Magma G] (h : Equation21314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21316_implies_Equation2 (G : Type*) [Magma G] (h : Equation21316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21317_implies_Equation2 (G : Type*) [Magma G] (h : Equation21317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21318_implies_Equation2 (G : Type*) [Magma G] (h : Equation21318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21319_implies_Equation2 (G : Type*) [Magma G] (h : Equation21319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21320_implies_Equation2 (G : Type*) [Magma G] (h : Equation21320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X3) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21322_implies_Equation2 (G : Type*) [Magma G] (h : Equation21322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 X6 X7 : G) : (X0 ◇ (((X5 ◇ X6) ◇ X7) ◇ (X1 ◇ X2))) = X7 := superpose eq7 eq7
  have eq32 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq9
  have eq42 (X0 X5 : G) : X0 = X5 := superpose eq7 eq32
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq147 eq42


@[equational_result]
theorem Equation21323_implies_Equation2 (G : Type*) [Magma G] (h : Equation21323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq12
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq32
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq143 eq42


@[equational_result]
theorem Equation21324_implies_Equation2 (G : Type*) [Magma G] (h : Equation21324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ X0) = X6 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation21325_implies_Equation2 (G : Type*) [Magma G] (h : Equation21325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 X7 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X7) ◇ (((X5 ◇ X6) ◇ X0) ◇ X6))) = X7 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X7 : G) : ((X1 ◇ X2) ◇ X0) = X7 := superpose eq7 eq10
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation21326_implies_Equation2 (G : Type*) [Magma G] (h : Equation21326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X0) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation21328_implies_Equation2 (G : Type*) [Magma G] (h : Equation21328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21329_implies_Equation2 (G : Type*) [Magma G] (h : Equation21329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21330_implies_Equation2 (G : Type*) [Magma G] (h : Equation21330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21331_implies_Equation2 (G : Type*) [Magma G] (h : Equation21331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21332_implies_Equation2 (G : Type*) [Magma G] (h : Equation21332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X1) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21334_implies_Equation2 (G : Type*) [Magma G] (h : Equation21334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21335_implies_Equation2 (G : Type*) [Magma G] (h : Equation21335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21336_implies_Equation2 (G : Type*) [Magma G] (h : Equation21336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21337_implies_Equation2 (G : Type*) [Magma G] (h : Equation21337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21338_implies_Equation2 (G : Type*) [Magma G] (h : Equation21338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X2) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21340_implies_Equation2 (G : Type*) [Magma G] (h : Equation21340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21341_implies_Equation2 (G : Type*) [Magma G] (h : Equation21341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21342_implies_Equation2 (G : Type*) [Magma G] (h : Equation21342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21343_implies_Equation2 (G : Type*) [Magma G] (h : Equation21343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21344_implies_Equation2 (G : Type*) [Magma G] (h : Equation21344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X3) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21346_implies_Equation2 (G : Type*) [Magma G] (h : Equation21346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21347_implies_Equation2 (G : Type*) [Magma G] (h : Equation21347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21348_implies_Equation2 (G : Type*) [Magma G] (h : Equation21348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21349_implies_Equation2 (G : Type*) [Magma G] (h : Equation21349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21350_implies_Equation2 (G : Type*) [Magma G] (h : Equation21350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21352_implies_Equation2 (G : Type*) [Magma G] (h : Equation21352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X5) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21353_implies_Equation2 (G : Type*) [Magma G] (h : Equation21353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X5) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21354_implies_Equation2 (G : Type*) [Magma G] (h : Equation21354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X5) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21355_implies_Equation2 (G : Type*) [Magma G] (h : Equation21355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X5) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21356_implies_Equation2 (G : Type*) [Magma G] (h : Equation21356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X5) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21357_implies_Equation2 (G : Type*) [Magma G] (h : Equation21357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X5) ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21566_implies_Equation2 (G : Type*) [Magma G] (h : Equation21566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq11
  have eq15 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq18 eq9
  have eq32 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq26 eq26
  have eq35 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq26 eq26
  have eq42 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq18
  have eq49 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq18 eq11
  have eq51 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq18 eq11
  have eq52 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq35 eq42
  have eq53 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq18 eq52
  have eq57 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq53 eq14
  have eq58 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq53 eq15
  have eq86 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq53 eq49
  have eq87 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq53 eq86
  have eq89 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq53 eq51
  have eq102 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq53 eq26
  have eq109 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq58 eq32
  have eq222 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq109 eq57
  have eq543 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq87 eq89
  have eq584 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq87 eq543
  have eq585 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq584 eq222
  have eq611 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq585 eq102
  have eq623 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq585 eq611
  have eq635 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq623 eq35
  have eq687 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq623 eq635
  have eq692 (X0 X2 : G) : X0 = X2 := superpose eq687 eq687
  have eq697 (X0 : G) : sK0 ≠ X0 := superpose eq692 eq8
  subsumption eq697 eq692


@[equational_result]
theorem Equation21568_implies_Equation2 (G : Type*) [Magma G] (h : Equation21568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq11
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq11 eq11
  have eq30 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (((X0 ◇ X2) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq11 eq9
  have eq32 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq7 eq9
  have eq51 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq19 eq19
  have eq52 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq19 eq19
  have eq64 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq51 eq30
  have eq65 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq51 eq32
  have eq96 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq52 eq10
  have eq222 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)) := superpose eq96 eq64
  have eq287 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq65 eq18
  have eq306 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq65 eq287
  have eq307 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq306 eq18
  have eq317 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq306 eq307
  have eq326 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ X0) := superpose eq317 eq222
  have eq376 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq317 eq326
  have eq377 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq317 eq376
  have eq378 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq317 eq377
  have eq379 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq317 eq378
  have eq420 (X0 X2 : G) : X0 = X2 := superpose eq379 eq379
  have eq428 (X0 : G) : sK0 ≠ X0 := superpose eq420 eq8
  subsumption eq428 eq420


@[equational_result]
theorem Equation21569_implies_Equation2 (G : Type*) [Magma G] (h : Equation21569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq7 eq11
  have eq16 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq11
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq7 eq11
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq16 eq13
  have eq32 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq10
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq10 eq7
  have eq39 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq23 eq32
  have eq44 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X0) := superpose eq39 eq17
  have eq46 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq39 eq44
  have eq48 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq39 eq35
  have eq49 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq39 eq48
  have eq55 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq16 eq49
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq16 eq55
  have eq60 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq58 eq46
  have eq63 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq58 eq60
  have eq64 (X0 X1 : G) : X0 = X1 := superpose eq39 eq63
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq72 eq64


@[equational_result]
theorem Equation21570_implies_Equation2 (G : Type*) [Magma G] (h : Equation21570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq11
  have eq32 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq10
  have eq46 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq16 eq16
  have eq49 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq16 eq7
  have eq56 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq46 eq32
  have eq59 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq46 eq49
  have eq60 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq59 eq56
  have eq61 (X1 X3 X4 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X4))) = X1 := superpose eq60 eq10
  have eq69 (X1 X3 X4 : G) : (X1 ◇ (X3 ◇ X4)) = X1 := superpose eq60 eq61
  have eq70 (X1 X4 : G) : (X1 ◇ X4) = X1 := superpose eq60 eq69
  have eq74 (X0 X1 : G) : X0 = X1 := superpose eq70 eq60
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq76 eq74


@[equational_result]
theorem Equation21573_implies_Equation2 (G : Type*) [Magma G] (h : Equation21573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq7 eq11
  have eq27 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq13 eq13
  have eq43 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) = X2 := superpose eq13 eq12
  have eq58 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq27
  have eq64 (X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) = X2 := superpose eq58 eq43
  have eq65 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq64 eq12
  have eq73 (X0 X2 : G) : X0 = X2 := superpose eq7 eq65
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq96 eq73


@[equational_result]
theorem Equation21576_implies_Equation2 (G : Type*) [Magma G] (h : Equation21576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq9 eq9
  have eq21 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X3))) = X1 := superpose eq21 eq16
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) := superpose eq9 eq10
  have eq49 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq21 eq10
  have eq51 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq21 eq7
  have eq53 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq21 eq7
  have eq55 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq21 eq9
  have eq61 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq53 eq49
  have eq65 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq61 eq21
  have eq74 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq65 eq9
  have eq78 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq55 eq74
  have eq79 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq51 eq78
  have eq90 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X1)) = X2 := superpose eq53 eq10
  have eq147 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq90
  have eq185 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq147 eq61
  have eq192 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq185 eq79
  have eq203 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq192
  have eq204 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := superpose eq203 eq7
  have eq206 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq203 eq10
  have eq217 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ X3) ◇ X3)) := superpose eq203 eq30
  have eq259 (X1 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X3))) = X1 := superpose eq204 eq28
  have eq263 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq203 eq206
  have eq284 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X2 ◇ X3) ◇ X3)) := superpose eq203 eq217
  have eq285 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X3)) := superpose eq203 eq284
  have eq286 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq263 eq285
  have eq288 (X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = X1 := superpose eq286 eq259
  have eq291 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq288 eq286
  have eq292 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq291 eq263
  have eq296 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq291 eq292
  have eq297 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq291 eq296
  have eq323 (X0 X2 : G) : X0 = X2 := superpose eq297 eq297
  have eq325 (X0 : G) : sK0 ≠ X0 := superpose eq323 eq8
  subsumption eq325 eq323


@[equational_result]
theorem Equation21578_implies_Equation2 (G : Type*) [Magma G] (h : Equation21578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X3 ◇ X1))) := superpose eq9 eq9
  have eq24 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X3 ◇ X1))) = X1 := superpose eq24 eq17
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) := superpose eq9 eq11
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) ◇ (X2 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0))))) = X1 := superpose eq11 eq7
  have eq42 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X2 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq11 eq9
  have eq44 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq7
  have eq46 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := superpose eq7 eq39
  have eq50 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq46 eq11
  have eq52 (X0 X1 X2 : G) : (X0 ◇ (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X2 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))))) = X1 := superpose eq46 eq41
  have eq53 (X0 X1 X2 : G) : (X0 ◇ (((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X2 ◇ ((((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))))) = X1 := superpose eq46 eq52
  have eq54 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := superpose eq42 eq46
  have eq58 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq54 eq50
  have eq60 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X2 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))))) = X1 := superpose eq54 eq53
  have eq62 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := superpose eq44 eq60
  have eq66 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ (X2 ◇ X3)) := superpose eq9 eq44
  have eq82 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0))))) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq44 eq9
  have eq86 (X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X1 := superpose eq62 eq82
  have eq87 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ (X2 ◇ X3)) := superpose eq86 eq66
  have eq98 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq44 eq58
  have eq109 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := superpose eq98 eq7
  have eq118 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq98 eq42
  have eq141 (X1 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X1))) = X1 := superpose eq109 eq33
  have eq153 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X2 ◇ X0)) = X1 := superpose eq98 eq118
  have eq154 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq153 eq87
  have eq155 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq154 eq109
  have eq157 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq154 eq141
  have eq163 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq157 eq155
  have eq165 (X0 X3 : G) : X0 = X3 := superpose eq163 eq163
  have eq167 (X0 : G) : sK0 ≠ X0 := superpose eq165 eq8
  subsumption eq167 eq165


@[equational_result]
theorem Equation21579_implies_Equation2 (G : Type*) [Magma G] (h : Equation21579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X1 := superpose eq11 eq11
  have eq31 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X3)))) = (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X4 ◇ X4))) := superpose eq7 eq9
  have eq66 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X3)))) = X2 := superpose eq16 eq31
  have eq67 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq7 eq66
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq7 eq67
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq147 eq68


@[equational_result]
theorem Equation21580_implies_Equation2 (G : Type*) [Magma G] (h : Equation21580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X2)) = X3 := superpose eq7 eq12
  have eq39 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq25 eq12
  have eq46 (X0 X2 : G) : X0 = X2 := superpose eq7 eq39
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq100 eq46


@[equational_result]
theorem Equation21582_implies_Equation2 (G : Type*) [Magma G] (h : Equation21582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq12 eq12
  have eq58 (X0 X2 : G) : X0 = X2 := superpose eq7 eq16
  have eq111 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq111 eq58


@[equational_result]
theorem Equation21583_implies_Equation2 (G : Type*) [Magma G] (h : Equation21583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq9
  have eq21 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq9
  have eq26 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq21
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0))) = X0 := superpose eq26 eq10
  have eq39 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq26 eq10
  have eq51 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq20 eq39
  have eq53 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq51 eq26
  have eq61 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq7 eq53
  have eq63 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq53 eq7
  have eq68 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq63 eq61
  have eq78 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq68 eq51
  have eq79 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq68 eq53
  have eq84 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq79 eq78
  have eq85 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq84 eq7
  have eq86 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq84 eq10
  have eq88 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) = X0 := superpose eq84 eq36
  have eq92 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq84 eq63
  have eq101 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq84 eq86
  have eq147 (X0 X1 X2 X4 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ X1) ◇ ((X4 ◇ (X1 ◇ X4)) ◇ X1)) := superpose eq101 eq101
  have eq148 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq84 eq101
  have eq156 (X1 X2 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq88 eq147
  have eq166 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq156 eq148
  have eq167 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq92 eq166
  have eq168 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq167 eq85
  have eq178 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq167 eq168
  have eq179 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq167 eq178
  have eq201 (X0 X1 : G) : X0 = X1 := superpose eq179 eq167
  have eq203 (X0 : G) : sK0 ≠ X0 := superpose eq201 eq8
  subsumption eq203 eq201


@[equational_result]
theorem Equation21584_implies_Equation2 (G : Type*) [Magma G] (h : Equation21584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq125 eq38


@[equational_result]
theorem Equation21586_implies_Equation2 (G : Type*) [Magma G] (h : Equation21586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = X1 := superpose eq7 eq12
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X1 := superpose eq13 eq11
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq7 eq24
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq47 eq29


@[equational_result]
theorem Equation21588_implies_Equation2 (G : Type*) [Magma G] (h : Equation21588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X2 := superpose eq12 eq11
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq45 eq18


@[equational_result]
theorem Equation21591_implies_Equation2 (G : Type*) [Magma G] (h : Equation21591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq7 eq9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X2 ◇ X2))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq12
  have eq27 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq26 eq11
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq27 eq10
  have eq50 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq28 eq28
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq28 eq50
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq69 eq51


@[equational_result]
theorem Equation21592_implies_Equation2 (G : Type*) [Magma G] (h : Equation21592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq134 eq50


@[equational_result]
theorem Equation21594_implies_Equation2 (G : Type*) [Magma G] (h : Equation21594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq12 eq12
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq166 eq61


@[equational_result]
theorem Equation21595_implies_Equation2 (G : Type*) [Magma G] (h : Equation21595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq132 eq49


@[equational_result]
theorem Equation21596_implies_Equation2 (G : Type*) [Magma G] (h : Equation21596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation21597_implies_Equation2 (G : Type*) [Magma G] (h : Equation21597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation21600_implies_Equation2 (G : Type*) [Magma G] (h : Equation21600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq7 eq10
  have eq15 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq10 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq15 eq12
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq19
  have eq52 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq21 eq21
  have eq55 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq21 eq10
  have eq61 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq21 eq55
  have eq68 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq61 eq52
  have eq70 (X0 X2 : G) : X0 = X2 := superpose eq68 eq68
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq78 eq70


@[equational_result]
theorem Equation21603_implies_Equation2 (G : Type*) [Magma G] (h : Equation21603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq10 eq10
  have eq18 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq10 eq7
  have eq19 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq7
  have eq21 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq16 eq18
  have eq94 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ X0) := superpose eq15 eq12
  have eq129 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq10 eq9
  have eq131 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1)) = (((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ ((X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq9 eq9
  have eq157 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) := superpose eq7 eq129
  have eq158 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq157 eq94
  have eq159 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq15 eq158
  have eq160 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq21 eq159
  have eq180 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq160 eq160
  have eq202 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq160 eq180
  have eq203 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq202
  have eq263 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq203
  have eq283 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3))) := superpose eq203 eq9
  have eq294 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq263 eq12
  have eq365 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq19
  have eq366 (X0 X1 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) = X0 := superpose eq17 eq19
  have eq367 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq11 eq19
  have eq386 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq19 eq294
  have eq397 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq294 eq366
  have eq398 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq397 eq263
  have eq429 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) = X0 := superpose eq398 eq157
  have eq443 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = (((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) ◇ X1) := superpose eq398 eq365
  have eq452 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1)) = (((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ ((X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1)) ◇ (X1 ◇ X2))) := superpose eq398 eq131
  have eq478 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X1 := superpose eq429 eq443
  have eq479 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3))) := superpose eq478 eq283
  have eq490 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = (((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2))) := superpose eq398 eq452
  have eq491 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X1 ◇ X2)) := superpose eq478 eq490
  have eq492 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := superpose eq478 eq491
  have eq493 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq492 eq479
  have eq494 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq398 eq493
  have eq497 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq494 eq367
  have eq498 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq398 eq497
  have eq499 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq498 eq494
  have eq501 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq499 eq398
  have eq524 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq499 eq386
  have eq525 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq501 eq524
  have eq526 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq499 eq525
  have eq527 (X0 X2 : G) : X0 = X2 := superpose eq526 eq526
  have eq532 (X0 : G) : sK0 ≠ X0 := superpose eq527 eq8
  subsumption eq532 eq527


@[equational_result]
theorem Equation21605_implies_Equation2 (G : Type*) [Magma G] (h : Equation21605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ (X4 ◇ (X1 ◇ X0))) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq10
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq10
  have eq47 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X3))) = ((((X0 ◇ X1) ◇ X2) ◇ (((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X3))) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) := superpose eq12 eq12
  have eq61 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X4 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq7 eq9
  have eq79 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X3)) = (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := superpose eq11 eq9
  have eq107 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0) := superpose eq7 eq14
  have eq113 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq14 eq9
  have eq114 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq10
  have eq120 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq14 eq7
  have eq135 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq114 eq113
  have eq137 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq114 eq107
  have eq142 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) := superpose eq137 eq16
  have eq154 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq114 eq120
  have eq159 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ X2) ◇ X2) = ((X0 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0)) := superpose eq142 eq142
  have eq169 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) = (((X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0)) ◇ X3) ◇ X3) := superpose eq142 eq142
  have eq230 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq142 eq169
  have eq237 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) := superpose eq230 eq47
  have eq283 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq230 eq237
  have eq284 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) := superpose eq230 eq283
  have eq285 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq137 eq284
  have eq286 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq135 eq285
  have eq287 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq286 eq7
  have eq290 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = (((X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X4 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq286 eq61
  have eq293 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) = X1 := superpose eq286 eq79
  have eq304 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq286 eq154
  have eq320 (X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X1 := superpose eq286 eq293
  have eq321 (X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X1) = X1 := superpose eq287 eq320
  have eq323 (X0 X2 X3 : G) : (((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ X2) ◇ X2) = ((X0 ◇ X2) ◇ X0) := superpose eq321 eq159
  have eq324 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq321 eq323
  have eq326 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = (((X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X4 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq324 eq290
  have eq328 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X1 := superpose eq324 eq321
  have eq330 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X4 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq324 eq326
  have eq335 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X4 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) := superpose eq328 eq330
  have eq359 (X0 X1 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1))))) = X1 := superpose eq304 eq335
  have eq366 (X0 X1 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = X1 := superpose eq304 eq359
  have eq367 (X1 X3 X4 : G) : (X3 ◇ X4) = X1 := superpose eq304 eq366
  have eq368 (X0 X3 : G) : X0 = X3 := superpose eq367 eq367
  have eq370 (X0 : G) : sK0 ≠ X0 := superpose eq368 eq8
  subsumption eq370 eq368


@[equational_result]
theorem Equation21606_implies_Equation2 (G : Type*) [Magma G] (h : Equation21606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq10
  have eq33 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq35 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ X1) = ((X2 ◇ (((X1 ◇ (X3 ◇ X3)) ◇ X1) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq10
  have eq39 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq14
  have eq42 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq14 eq14
  have eq47 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq14 eq7
  have eq63 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq42 eq33
  have eq65 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X1) = ((X2 ◇ (((X1 ◇ X3) ◇ X1) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq42 eq35
  have eq75 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq42 eq63
  have eq78 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq47 eq39
  have eq83 (X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X1) = ((X2 ◇ (((X1 ◇ X3) ◇ X1) ◇ X2)) ◇ X1) := superpose eq78 eq65
  have eq88 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq78 eq75
  have eq91 (X1 X3 : G) : ((X1 ◇ X3) ◇ X1) = (((X1 ◇ X3) ◇ X1) ◇ X1) := superpose eq78 eq83
  have eq94 (X1 X3 : G) : ((X1 ◇ X3) ◇ X1) = X1 := superpose eq88 eq91
  have eq112 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq94 eq94
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq112
  have eq116 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq114 eq78
  have eq118 (X0 X1 : G) : X0 = X1 := superpose eq114 eq116
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq120 eq118


@[equational_result]
theorem Equation21607_implies_Equation2 (G : Type*) [Magma G] (h : Equation21607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq18 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq10 eq7
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq15
  have eq60 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq21 eq10
  have eq66 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq60 eq21
  have eq74 (X0 X1 : G) : X0 = X1 := superpose eq66 eq60
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq87 eq74


@[equational_result]
theorem Equation21610_implies_Equation2 (G : Type*) [Magma G] (h : Equation21610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) = X1 := superpose eq7 eq7
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq10
  have eq41 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq16
  have eq47 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq41 eq12
  have eq49 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := superpose eq41 eq9
  have eq60 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq47 eq49
  have eq61 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq47 eq60
  have eq62 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq47 eq61
  have eq70 (X0 X2 : G) : X0 = X2 := superpose eq62 eq62
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq78 eq70


@[equational_result]
theorem Equation21613_implies_Equation2 (G : Type*) [Magma G] (h : Equation21613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq10 eq10
  have eq100 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq16
  have eq161 (X0 X2 : G) : X0 = X2 := superpose eq15 eq100
  have eq275 (X0 : G) : sK0 ≠ X0 := superpose eq161 eq8
  subsumption eq275 eq161


@[equational_result]
theorem Equation21615_implies_Equation2 (G : Type*) [Magma G] (h : Equation21615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X4)) = X3 := superpose eq10 eq10
  have eq23 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq7 eq9
  have eq42 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X2 := superpose eq9 eq7
  have eq53 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X2 := superpose eq7 eq42
  have eq59 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = X1 := superpose eq16 eq16
  have eq82 (X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = X1 := superpose eq59 eq23
  have eq84 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq82 eq53
  have eq85 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq84 eq82
  have eq100 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := superpose eq85 eq7
  have eq107 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq85 eq100
  have eq108 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq85 eq107
  have eq119 (X0 X2 : G) : X0 = X2 := superpose eq108 eq108
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq121 eq119


@[equational_result]
theorem Equation21616_implies_Equation2 (G : Type*) [Magma G] (h : Equation21616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = X1 := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq9
  have eq34 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) := superpose eq10 eq9
  have eq48 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq14 eq22
  have eq57 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq48 eq48
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X2)) := superpose eq48 eq10
  have eq65 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq57 eq34
  have eq67 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq65 eq48
  have eq156 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq67
  have eq168 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq156 eq58
  have eq171 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) = X2 := superpose eq168 eq11
  have eq214 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X2 := superpose eq168 eq171
  have eq215 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq168 eq214
  have eq218 (X0 X3 : G) : X0 = X3 := superpose eq215 eq215
  have eq224 (X0 : G) : sK0 ≠ X0 := superpose eq218 eq8
  subsumption eq224 eq218


@[equational_result]
theorem Equation21617_implies_Equation2 (G : Type*) [Magma G] (h : Equation21617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) = X1 := superpose eq7 eq7
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq42 (X0 X2 : G) : X0 = X2 := superpose eq7 eq32
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq99 eq42


@[equational_result]
theorem Equation21619_implies_Equation2 (G : Type*) [Magma G] (h : Equation21619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq10 eq7
  have eq46 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq89 (X0 X3 : G) : X0 = X3 := superpose eq7 eq46
  have eq217 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq217 eq89


@[equational_result]
theorem Equation21621_implies_Equation2 (G : Type*) [Magma G] (h : Equation21621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X3))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq10 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq37 eq29


@[equational_result]
theorem Equation21623_implies_Equation2 (G : Type*) [Magma G] (h : Equation21623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = X1 := superpose eq7 eq11
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X1 := superpose eq12 eq10
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq11 eq20
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq44 eq26


@[equational_result]
theorem Equation21624_implies_Equation2 (G : Type*) [Magma G] (h : Equation21624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq7 eq10
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X0)) := superpose eq24 eq10
  have eq39 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq32
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq7 eq32
  have eq65 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X0)) = X2 := superpose eq39 eq11
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq46 eq65
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq7 eq71
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq102 eq72


@[equational_result]
theorem Equation21625_implies_Equation2 (G : Type*) [Magma G] (h : Equation21625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq11
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation21628_implies_Equation2 (G : Type*) [Magma G] (h : Equation21628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X3 ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := superpose eq10 eq9
  have eq54 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ X3))) = X0 := superpose eq7 eq23
  have eq64 (X0 X3 : G) : X0 = X3 := superpose eq7 eq54
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq163 eq64


@[equational_result]
theorem Equation21629_implies_Equation2 (G : Type*) [Magma G] (h : Equation21629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X3))) = X1 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq51 eq20


@[equational_result]
theorem Equation21631_implies_Equation2 (G : Type*) [Magma G] (h : Equation21631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq11 eq11
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq128 eq42


@[equational_result]
theorem Equation21632_implies_Equation2 (G : Type*) [Magma G] (h : Equation21632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq152 eq56


@[equational_result]
theorem Equation21633_implies_Equation2 (G : Type*) [Magma G] (h : Equation21633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq139 eq33


@[equational_result]
theorem Equation21634_implies_Equation2 (G : Type*) [Magma G] (h : Equation21634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X5))) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation21636_implies_Equation2 (G : Type*) [Magma G] (h : Equation21636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq10
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq22 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq16 eq14
  have eq32 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X4 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X4))) := superpose eq10 eq9
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq9
  have eq52 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq7
  have eq60 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq22 eq52
  have eq61 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq60 eq36
  have eq120 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq60 eq11
  have eq136 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq60 eq120
  have eq137 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq22 eq136
  have eq142 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X4 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq137 eq32
  have eq156 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq137 eq7
  have eq185 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq156 eq61
  have eq189 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq22 eq185
  have eq190 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq189 eq142
  have eq205 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq190 eq189
  have eq231 (X0 X1 : G) : X0 = X1 := superpose eq190 eq205
  have eq233 (X0 : G) : sK0 ≠ X0 := superpose eq231 eq8
  subsumption eq233 eq231


@[equational_result]
theorem Equation21637_implies_Equation2 (G : Type*) [Magma G] (h : Equation21637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq9
  have eq13 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9
  have eq17 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq7
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq12
  have eq20 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq18 eq17
  have eq25 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq9 eq10
  have eq33 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq20 eq25
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq20 eq33
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq34 eq7
  have eq44 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq34 eq35
  have eq45 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq34 eq44
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq45 eq45
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq54 eq52


@[equational_result]
theorem Equation21638_implies_Equation2 (G : Type*) [Magma G] (h : Equation21638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X4 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X4))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq10 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq16 eq12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq16 eq20
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq22 eq9
  have eq27 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X2 := superpose eq22 eq23
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq27 eq27
  have eq33 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq31 eq22
  have eq34 (X0 X1 : G) : X0 = X1 := superpose eq31 eq33
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq36 eq34


@[equational_result]
theorem Equation21640_implies_Equation2 (G : Type*) [Magma G] (h : Equation21640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) := superpose eq7 eq11
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq11
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) := superpose eq16 eq14
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X1 := superpose eq16 eq11
  have eq39 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq16
  have eq42 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq16 eq7
  have eq46 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq16 eq39
  have eq72 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq46 eq25
  have eq85 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq25 eq23
  have eq86 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X1 ◇ X2)) = ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq23 eq23
  have eq96 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1)) := superpose eq23 eq42
  have eq101 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq42 eq23
  have eq112 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq46 eq101
  have eq113 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq46 eq112
  have eq114 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq113 eq72
  have eq118 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq114 eq85
  have eq119 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq46 eq118
  have eq122 (X1 X3 : G) : (X3 ◇ X1) = X3 := superpose eq119 eq96
  have eq136 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X1 := superpose eq119 eq86
  have eq159 (X0 X1 X4 : G) : (((X0 ◇ X4) ◇ X1) ◇ X0) = X1 := superpose eq122 eq136
  have eq160 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ X0) = X1 := superpose eq122 eq159
  have eq161 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq122 eq160
  have eq170 (X0 X2 : G) : X0 = X2 := superpose eq161 eq161
  have eq178 (X0 : G) : sK0 ≠ X0 := superpose eq170 eq8
  subsumption eq178 eq170


@[equational_result]
theorem Equation21641_implies_Equation2 (G : Type*) [Magma G] (h : Equation21641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2)))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2))))) = X0 := superpose eq7 eq10
  have eq23 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq15
  have eq55 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq23
  have eq76 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2))) ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)))) := superpose eq12 eq12
  have eq80 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) := superpose eq23 eq12
  have eq104 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq55 eq80
  have eq105 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq55 eq104
  have eq106 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq23 eq105
  have eq109 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq106 eq7
  have eq150 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq106 eq76
  have eq153 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq106 eq109
  have eq154 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq106 eq153
  have eq188 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1))) ◇ X1) := superpose eq106 eq150
  have eq189 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq154 eq188
  have eq190 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq106 eq189
  have eq191 (X0 X1 : G) : X0 = X1 := superpose eq23 eq190
  have eq199 (X0 : G) : sK0 ≠ X0 := superpose eq191 eq8
  subsumption eq199 eq191


@[equational_result]
theorem Equation21642_implies_Equation2 (G : Type*) [Magma G] (h : Equation21642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X4))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq10
  have eq19 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq10 eq7
  have eq22 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X5))) = X0 := superpose eq10 eq7
  have eq45 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq17
  have eq58 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq19 eq45
  have eq59 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq58 eq19
  have eq71 (X0 X1 X2 X3 X5 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = ((X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X5)) ◇ X1) := superpose eq12 eq12
  have eq72 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq12
  have eq91 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq59 eq72
  have eq92 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq59 eq91
  have eq103 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq92 eq22
  have eq114 (X1 X2 X5 : G) : (X1 ◇ X2) = ((X1 ◇ ((X1 ◇ X2) ◇ X5)) ◇ X1) := superpose eq92 eq71
  have eq121 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X1) := superpose eq92 eq114
  have eq122 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq103 eq121
  have eq124 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq122 eq92
  have eq128 (X0 X1 : G) : X0 = X1 := superpose eq59 eq124
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq128 eq8
  subsumption eq136 eq128


@[equational_result]
theorem Equation21645_implies_Equation2 (G : Type*) [Magma G] (h : Equation21645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq10
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))))) = X0 := superpose eq10 eq7
  have eq24 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq10 eq11
  have eq25 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ X0)) := superpose eq11 eq11
  have eq26 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq11
  have eq34 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq24 eq15
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq34 eq24
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))))) = X0 := superpose eq34 eq18
  have eq40 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq13 eq25
  have eq41 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq26 eq40
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X2 := superpose eq26 eq11
  have eq44 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq43 eq35
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := superpose eq44 eq37
  have eq55 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq26 eq45
  have eq56 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq55 eq41
  have eq57 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq55 eq56
  have eq58 (X0 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq57 eq43
  have eq61 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq57 eq58
  have eq79 (X0 X2 : G) : X0 = X2 := superpose eq61 eq61
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq81 eq79


@[equational_result]
theorem Equation21646_implies_Equation2 (G : Type*) [Magma G] (h : Equation21646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4)))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq10
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq10
  have eq29 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) := superpose eq7 eq11
  have eq30 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq10 eq11
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq15
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq15 eq11
  have eq61 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq45 eq12
  have eq65 (X0 X1 X5 : G) : (X1 ◇ X0) = ((X5 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq10 eq61
  have eq94 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq65 eq29
  have eq95 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq52 eq94
  have eq96 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq95 eq18
  have eq105 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq95 eq30
  have eq128 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq96 eq105
  have eq129 (X0 X3 : G) : X0 = X3 := superpose eq128 eq128
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq134 eq129


@[equational_result]
theorem Equation21648_implies_Equation2 (G : Type*) [Magma G] (h : Equation21648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ (X4 ◇ (X1 ◇ (X0 ◇ X2))))) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq10
  have eq19 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq10
  have eq23 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X5 ◇ X1))) = X0 := superpose eq10 eq7
  have eq55 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq19 eq7
  have eq99 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq17
  have eq108 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq17 eq7
  have eq123 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq108 eq99
  have eq126 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq123 eq55
  have eq134 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X5) = X0 := superpose eq123 eq23
  have eq174 (X0 X1 X5 : G) : (X1 ◇ X5) = X0 := superpose eq126 eq134
  have eq175 (X0 X1 : G) : X0 = X1 := superpose eq19 eq174
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq175 eq8
  subsumption eq183 eq175


@[equational_result]
theorem Equation21649_implies_Equation2 (G : Type*) [Magma G] (h : Equation21649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ (X4 ◇ (X3 ◇ X2)))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X4 ◇ X3))) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq10
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq10
  have eq30 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq11
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq18 eq30
  have eq56 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq18 eq7
  have eq62 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq46 eq56
  have eq71 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X1))) ◇ X0) := superpose eq18 eq12
  have eq101 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ X1)) ◇ X0) := superpose eq62 eq71
  have eq103 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq101 eq17
  have eq114 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X2 ◇ X0)) = X2 := superpose eq103 eq11
  have eq132 (X0 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X0)) = X2 := superpose eq103 eq114
  have eq133 (X0 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X2 ◇ X0)) = X2 := superpose eq103 eq132
  have eq134 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq133 eq62
  have eq136 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq134 eq46
  have eq170 (X0 X1 : G) : X0 = X1 := superpose eq136 eq134
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq170 eq8
  subsumption eq191 eq170


@[equational_result]
theorem Equation21650_implies_Equation2 (G : Type*) [Magma G] (h : Equation21650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 : G) : (X0 ◇ (X0 ◇ (X4 ◇ X4))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq10 eq7
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq17 eq14
  have eq24 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq10 eq11
  have eq38 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq24 eq15
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq38 eq19
  have eq56 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq38 eq40
  have eq64 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq56 eq40
  have eq66 (X0 X1 : G) : X0 = X1 := superpose eq38 eq64
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq74 eq66


@[equational_result]
theorem Equation21651_implies_Equation2 (G : Type*) [Magma G] (h : Equation21651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ (X0 ◇ (X5 ◇ X6))) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq10 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq17 eq15
  have eq24 (X0 X5 : G) : (X0 ◇ X5) = X0 := superpose eq21 eq10
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq24 eq21
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq24 eq29
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation21653_implies_Equation2 (G : Type*) [Magma G] (h : Equation21653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq10 eq7
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq18 eq10
  have eq60 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X1 := superpose eq45 eq10
  have eq72 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq60
  have eq83 (X0 X2 : G) : X0 = X2 := superpose eq7 eq72
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq165 eq83


@[equational_result]
theorem Equation21654_implies_Equation2 (G : Type*) [Magma G] (h : Equation21654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq48 eq11


@[equational_result]
theorem Equation21655_implies_Equation2 (G : Type*) [Magma G] (h : Equation21655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X4))) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq93 eq48


@[equational_result]
theorem Equation21657_implies_Equation2 (G : Type*) [Magma G] (h : Equation21657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3)) = (X0 ◇ ((X2 ◇ (X0 ◇ X4)) ◇ ((X2 ◇ (X0 ◇ X4)) ◇ (X2 ◇ (X0 ◇ X4))))) := superpose eq7 eq9
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ (X4 ◇ X4)) ◇ X5)) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X4 ◇ X1) ◇ ((X4 ◇ X1) ◇ (X4 ◇ X1)))) := superpose eq9 eq9
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq7 eq9
  have eq37 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3)) = X2 := superpose eq10 eq18
  have eq38 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X4 ◇ X1) ◇ ((X4 ◇ X1) ◇ (X4 ◇ X1)))) = X4 := superpose eq37 eq19
  have eq40 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X4) = X4 := superpose eq25 eq38
  have eq45 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq40 eq11
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq40 eq45
  have eq49 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq47 eq25
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := superpose eq49 eq7
  have eq60 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq49 eq52
  have eq61 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X0 := superpose eq49 eq60
  have eq62 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq49 eq61
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq62 eq62
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq65 eq63


@[equational_result]
theorem Equation21658_implies_Equation2 (G : Type*) [Magma G] (h : Equation21658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X3))))))) = X2 := superpose eq10 eq10
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) = ((X1 ◇ X3) ◇ (X1 ◇ X0)) := superpose eq10 eq9
  have eq61 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1)) = X0 := superpose eq9 eq11
  have eq90 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ (X2 ◇ X1)) = ((X1 ◇ X0) ◇ (X4 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)))))) := superpose eq10 eq33
  have eq113 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X1 ◇ X3)) ◇ (X4 ◇ X1)) = ((X1 ◇ (X4 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2)))) := superpose eq33 eq33
  have eq165 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X3) ◇ (X4 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))))) = X4 := superpose eq33 eq7
  have eq173 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2))) = X2 := superpose eq90 eq25
  have eq187 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := superpose eq7 eq173
  have eq211 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq173
  have eq234 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq211 eq9
  have eq348 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq211 eq234
  have eq350 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) := superpose eq348 eq187
  have eq356 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq211 eq350
  have eq358 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := superpose eq356 eq61
  have eq370 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))))) = X4 := superpose eq356 eq165
  have eq372 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X1 ◇ X3)) ◇ (X4 ◇ X1)) = ((X1 ◇ (X4 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X2))) := superpose eq356 eq113
  have eq400 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2)))) = X4 := superpose eq356 eq370
  have eq401 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X2))) = X4 := superpose eq356 eq400
  have eq402 (X1 X3 X4 : G) : ((X4 ◇ (X1 ◇ X3)) ◇ (X4 ◇ X1)) = X1 := superpose eq401 eq372
  have eq404 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq402 eq173
  have eq407 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X1) = X0 := superpose eq404 eq358
  have eq439 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = X0 := superpose eq404 eq407
  have eq440 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq404 eq439
  have eq441 (X0 X3 : G) : X0 = X3 := superpose eq440 eq440
  have eq446 (X0 : G) : sK0 ≠ X0 := superpose eq441 eq8
  subsumption eq446 eq441


@[equational_result]
theorem Equation21659_implies_Equation2 (G : Type*) [Magma G] (h : Equation21659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X4))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = (X0 ◇ ((X2 ◇ (X0 ◇ X5)) ◇ ((X2 ◇ (X0 ◇ X5)) ◇ X6))) := superpose eq7 eq9
  have eq19 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X3 ◇ ((X4 ◇ (X4 ◇ X5)) ◇ X6)) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X4 ◇ X1) ◇ ((X4 ◇ X1) ◇ X7))) := superpose eq9 eq9
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq7 eq9
  have eq37 (X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = X2 := superpose eq10 eq18
  have eq38 (X0 X1 X2 X4 X7 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X4 ◇ X1) ◇ ((X4 ◇ X1) ◇ X7))) = X4 := superpose eq37 eq19
  have eq39 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X4) = X4 := superpose eq25 eq38
  have eq44 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq39 eq11
  have eq47 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = X3 := superpose eq39 eq44
  have eq48 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq47 eq25
  have eq52 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := superpose eq48 eq7
  have eq60 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = X0 := superpose eq48 eq52
  have eq61 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq48 eq60
  have eq62 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq48 eq61
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq62 eq62
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq65 eq63


@[equational_result]
theorem Equation21662_implies_Equation2 (G : Type*) [Magma G] (h : Equation21662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X3))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ X3)) := superpose eq7 eq9
  have eq26 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq13
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq26 eq10
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq39
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq65 eq40


@[equational_result]
theorem Equation21663_implies_Equation2 (G : Type*) [Magma G] (h : Equation21663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X4))) = X1 := superpose eq7 eq7
  have eq38 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq38
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq130 eq47


@[equational_result]
theorem Equation21665_implies_Equation2 (G : Type*) [Magma G] (h : Equation21665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ (X5 ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X3) ◇ (X4 ◇ X5)) ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))))) = X4 := superpose eq9 eq7
  have eq45 (X0 X1 X3 X4 X5 : G) : (((X1 ◇ X3) ◇ (X4 ◇ X5)) ◇ X0) = X4 := superpose eq28 eq33
  have eq47 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq45 eq12
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq7 eq47
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq73 eq48


@[equational_result]
theorem Equation21666_implies_Equation2 (G : Type*) [Magma G] (h : Equation21666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X3 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq136 eq54


@[equational_result]
theorem Equation21667_implies_Equation2 (G : Type*) [Magma G] (h : Equation21667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X4 ◇ X4))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq11 eq10
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq7 eq32
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq122 eq44


@[equational_result]
theorem Equation21668_implies_Equation2 (G : Type*) [Magma G] (h : Equation21668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X5 ◇ X6))) = X1 := superpose eq7 eq7
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq32
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq109 eq42


@[equational_result]
theorem Equation21671_implies_Equation2 (G : Type*) [Magma G] (h : Equation21671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0)) = X2 := superpose eq9 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X4 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (((X3 ◇ (X0 ◇ X3)) ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)))) := superpose eq7 eq10
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X4)) = ((X5 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq10 eq10
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq10 eq10
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X1) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq10 eq9
  have eq36 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq28
  have eq83 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq36 eq14
  have eq91 (X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X4)) = ((X5 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq83 eq26
  have eq97 (X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X4)) = X1 := superpose eq7 eq91
  have eq99 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X1) = ((X3 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq97 eq34
  have eq102 (X1 X2 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq36 eq99
  have eq103 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X4 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) := superpose eq102 eq22
  have eq106 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq83 eq103
  have eq108 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq106 eq7
  have eq115 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq106 eq108
  have eq116 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq106 eq115
  have eq119 (X0 X2 : G) : X0 = X2 := superpose eq116 eq116
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq121 eq119


@[equational_result]
theorem Equation21672_implies_Equation2 (G : Type*) [Magma G] (h : Equation21672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq10 eq10
  have eq23 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq14 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation21675_implies_Equation2 (G : Type*) [Magma G] (h : Equation21675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X3))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X4)) = (X0 ◇ ((X4 ◇ (X1 ◇ X4)) ◇ (X3 ◇ (X4 ◇ (X1 ◇ X4))))) := superpose eq10 eq9
  have eq28 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (((X1 ◇ (X0 ◇ X3)) ◇ X2) ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X0)) := superpose eq7 eq9
  have eq32 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2)) = X0 := superpose eq7 eq9
  have eq47 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq32 eq32
  have eq53 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq32 eq7
  have eq56 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X4)) ◇ (X3 ◇ (X4 ◇ (X1 ◇ X4))))) = (X1 ◇ (((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2) ◇ X4)) := superpose eq32 eq9
  have eq83 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) = X2 := superpose eq7 eq11
  have eq84 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X3 ◇ (X0 ◇ X3)) ◇ (X2 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X2)) ◇ (X4 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq9 eq11
  have eq113 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))))) ◇ X0) = X2 := superpose eq7 eq47
  have eq144 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X5 ◇ (X2 ◇ (X0 ◇ X2)))))) = (((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) ◇ ((((X2 ◇ (X0 ◇ X2)) ◇ (X5 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X5 ◇ (X2 ◇ (X0 ◇ X2)))))) ◇ (X5 ◇ X1))) := superpose eq9 eq28
  have eq157 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) = (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq7 eq28
  have eq205 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ X0) = X2 := superpose eq157 eq113
  have eq219 (X0 X1 X2 X3 : G) : (((X2 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)))) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ X2) = X3 := superpose eq9 eq53
  have eq238 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X1 := superpose eq53 eq53
  have eq262 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)))) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)))) ◇ X2) = X3 := superpose eq157 eq219
  have eq263 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)))) ◇ X2) = X3 := superpose eq32 eq262
  have eq264 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)))) ◇ X2) = X3 := superpose eq7 eq263
  have eq306 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0) := superpose eq83 eq47
  have eq393 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq205 eq32
  have eq425 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) = X2 := superpose eq393 eq83
  have eq438 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0) := superpose eq393 eq306
  have eq508 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2))))) := superpose eq32 eq425
  have eq548 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq7 eq508
  have eq563 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X0))) ◇ X2) = X3 := superpose eq548 eq264
  have eq609 (X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = X2 := superpose eq563 eq438
  have eq610 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq609 eq238
  have eq721 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq609 eq610
  have eq724 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (X1 ◇ (((X2 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X4)) := superpose eq721 eq23
  have eq733 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (X1 ◇ (((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2) ◇ X4)) := superpose eq721 eq56
  have eq737 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X4 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq721 eq84
  have eq738 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X5)) = (((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) ◇ ((X5 ◇ (X3 ◇ X5)) ◇ (X5 ◇ X1))) := superpose eq721 eq144
  have eq848 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) := superpose eq721 eq724
  have eq855 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (X1 ◇ (((X0 ◇ X3) ◇ X2) ◇ X4)) := superpose eq721 eq733
  have eq858 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X4 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq721 eq737
  have eq859 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X4 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq609 eq858
  have eq860 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq721 eq859
  have eq861 (X3 X4 X5 : G) : (X5 ◇ X3) = (X3 ◇ (X4 ◇ X5)) := superpose eq848 eq738
  have eq872 (X0 X3 X4 : G) : (X4 ◇ (X3 ◇ X0)) = X4 := superpose eq861 eq860
  have eq892 (X3 X5 : G) : (X5 ◇ X3) = X3 := superpose eq872 eq861
  have eq896 (X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ X2) ◇ X4)) = X3 := superpose eq892 eq855
  have eq908 (X1 X3 X4 : G) : (X1 ◇ X4) = X3 := superpose eq892 eq896
  have eq917 (X0 X3 : G) : X0 = X3 := superpose eq908 eq908
  have eq928 (X0 : G) : sK0 ≠ X0 := superpose eq917 eq8
  subsumption eq928 eq917


@[equational_result]
theorem Equation21676_implies_Equation2 (G : Type*) [Magma G] (h : Equation21676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X4 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X5) = X2 := superpose eq12 eq12
  have eq26 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X3 := superpose eq16 eq11
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq26
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq54 eq33


@[equational_result]
theorem Equation21679_implies_Equation2 (G : Type*) [Magma G] (h : Equation21679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq38 eq15


@[equational_result]
theorem Equation21680_implies_Equation2 (G : Type*) [Magma G] (h : Equation21680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X3 ◇ (X3 ◇ X4)) ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X4))) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X3 := superpose eq10 eq9
  have eq13 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq12 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation21682_implies_Equation2 (G : Type*) [Magma G] (h : Equation21682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X1) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq10 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq53 eq42


@[equational_result]
theorem Equation21683_implies_Equation2 (G : Type*) [Magma G] (h : Equation21683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X2) ◇ (X4 ◇ (X3 ◇ X2)))) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq46 eq17


@[equational_result]
theorem Equation21684_implies_Equation2 (G : Type*) [Magma G] (h : Equation21684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X4 ◇ X4))) = X2 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation21685_implies_Equation2 (G : Type*) [Magma G] (h : Equation21685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X5 ◇ X6))) = X2 := superpose eq7 eq7
  have eq22 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation21687_implies_Equation2 (G : Type*) [Magma G] (h : Equation21687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq7 eq12
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq119 eq42


@[equational_result]
theorem Equation21688_implies_Equation2 (G : Type*) [Magma G] (h : Equation21688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq9 eq9
  have eq21 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq13 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq35 eq24


@[equational_result]
theorem Equation21689_implies_Equation2 (G : Type*) [Magma G] (h : Equation21689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq106 eq36


@[equational_result]
theorem Equation21690_implies_Equation2 (G : Type*) [Magma G] (h : Equation21690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ (X3 ◇ X6))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq10 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq37 eq29


@[equational_result]
theorem Equation21692_implies_Equation2 (G : Type*) [Magma G] (h : Equation21692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = X1 := superpose eq7 eq12
  have eq23 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X3 := superpose eq13 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation21693_implies_Equation2 (G : Type*) [Magma G] (h : Equation21693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X4 ◇ (X1 ◇ X2)))) ◇ (X5 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X6 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X6) = X2 := superpose eq7 eq12
  have eq23 (X0 X3 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X3 := superpose eq13 eq11
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq12 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation21694_implies_Equation2 (G : Type*) [Magma G] (h : Equation21694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X4))) = X3 := superpose eq7 eq7
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq53 eq36


@[equational_result]
theorem Equation21695_implies_Equation2 (G : Type*) [Magma G] (h : Equation21695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X3 := superpose eq12 eq11
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation21697_implies_Equation2 (G : Type*) [Magma G] (h : Equation21697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 X6 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X6) = X4 := superpose eq7 eq12
  have eq24 (X0 X2 X4 X5 : G) : (X2 ◇ (X5 ◇ X0)) = X4 := superpose eq13 eq11
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq51 eq29


@[equational_result]
theorem Equation21698_implies_Equation2 (G : Type*) [Magma G] (h : Equation21698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq58 eq36


@[equational_result]
theorem Equation21699_implies_Equation2 (G : Type*) [Magma G] (h : Equation21699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X2 ◇ X3) ◇ X4))) = X3 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq42 eq19


@[equational_result]
theorem Equation21700_implies_Equation2 (G : Type*) [Magma G] (h : Equation21700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ ((X2 ◇ X4) ◇ X6))) = X3 := superpose eq7 eq7
  have eq34 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq54 eq34


@[equational_result]
theorem Equation21702_implies_Equation2 (G : Type*) [Magma G] (h : Equation21702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X1 ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq84 eq25


@[equational_result]
theorem Equation21703_implies_Equation2 (G : Type*) [Magma G] (h : Equation21703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X3 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq43 eq19


@[equational_result]
theorem Equation21704_implies_Equation2 (G : Type*) [Magma G] (h : Equation21704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ X4))) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq69 eq16


@[equational_result]
theorem Equation21705_implies_Equation2 (G : Type*) [Magma G] (h : Equation21705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ (X5 ◇ X6))) = X3 := superpose eq7 eq7
  have eq20 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq51 eq20


@[equational_result]
theorem Equation21707_implies_Equation2 (G : Type*) [Magma G] (h : Equation21707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ (X6 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = X5 := superpose eq7 eq12
  have eq23 (X0 X2 X4 X6 : G) : (X2 ◇ (X6 ◇ X0)) = X4 := superpose eq13 eq11
  have eq28 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq50 eq28


@[equational_result]
theorem Equation21708_implies_Equation2 (G : Type*) [Magma G] (h : Equation21708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X4 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq22 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation21709_implies_Equation2 (G : Type*) [Magma G] (h : Equation21709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X5))) = X3 := superpose eq7 eq7
  have eq20 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq51 eq20


@[equational_result]
theorem Equation21710_implies_Equation2 (G : Type*) [Magma G] (h : Equation21710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X6))) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation21711_implies_Equation2 (G : Type*) [Magma G] (h : Equation21711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X6 X7 X8 : G) : (X0 ◇ (X6 ◇ (X7 ◇ X8))) = X3 := superpose eq7 eq7
  have eq19 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation21717_implies_Equation2 (G : Type*) [Magma G] (h : Equation21717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq7 eq10
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq10 eq10
  have eq28 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0) = (((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0))) ◇ (X0 ◇ X2)) := superpose eq10 eq11
  have eq43 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq21
  have eq82 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq21 eq14
  have eq84 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X1))) := superpose eq14 eq9
  have eq86 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq14 eq7
  have eq93 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq14 eq11
  have eq97 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq14 eq82
  have eq123 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) = ((((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq7 eq43
  have eq125 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X0))) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (((X2 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X0)) := superpose eq10 eq43
  have eq129 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq14 eq43
  have eq130 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))))) = ((((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq43 eq43
  have eq132 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq9 eq43
  have eq157 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq7 eq129
  have eq158 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq14 eq157
  have eq160 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq158 eq93
  have eq173 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((((X2 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq10 eq23
  have eq201 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq7 eq132
  have eq203 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq132 eq11
  have eq208 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq132 eq21
  have eq235 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))) := superpose eq14 eq201
  have eq236 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq235 eq158
  have eq237 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq236 eq160
  have eq239 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq14 eq237
  have eq244 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq239 eq97
  have eq248 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq239 eq236
  have eq249 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq239 eq244
  have eq255 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq203 eq132
  have eq257 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq255 eq86
  have eq259 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq255 eq84
  have eq260 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq257
  have eq261 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq260 eq14
  have eq262 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq260 eq43
  have eq266 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))))) = ((((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq260 eq130
  have eq296 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq260 eq248
  have eq297 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq260 eq249
  have eq299 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq260 eq123
  have eq302 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X2 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X0))) := superpose eq260 eq125
  have eq308 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq262 eq11
  have eq345 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) = ((((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq262 eq266
  have eq346 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = ((((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq262 eq345
  have eq347 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq260 eq346
  have eq348 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq347
  have eq378 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq348 eq23
  have eq379 (X0 X2 : G) : (((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq348 eq28
  have eq386 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq348 eq173
  have eq471 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq261 eq296
  have eq472 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq261 eq297
  have eq473 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq308 eq472
  have eq474 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq473
  have eq475 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq474 eq471
  have eq491 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq348 eq299
  have eq502 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq348 eq302
  have eq504 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq502 eq379
  have eq505 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq504 eq386
  have eq525 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq475 eq259
  have eq526 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq475 eq525
  have eq527 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq475 eq526
  have eq528 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq475 eq527
  have eq541 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq491 eq208
  have eq542 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq348 eq541
  have eq543 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq505 eq542
  have eq544 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq348 eq543
  have eq545 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq378 eq544
  have eq546 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq545 eq7
  have eq551 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq545 eq308
  have eq590 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq545 eq528
  have eq659 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq590 eq545
  have eq670 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq659 eq546
  have eq671 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq659 eq551
  have eq695 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq659 eq670
  have eq696 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq659 eq671
  have eq701 (X0 X1 : G) : X0 = X1 := superpose eq695 eq696
  have eq706 (X0 : G) : sK0 ≠ X0 := superpose eq701 eq8
  subsumption eq706 eq701


@[equational_result]
theorem Equation21719_implies_Equation2 (G : Type*) [Magma G] (h : Equation21719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X4)) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq10
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq10
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X2) := superpose eq11 eq11
  have eq28 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) = (((X3 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X1) := superpose eq11 eq11
  have eq29 (X0 X1 X2 : G) : ((((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq11 eq10
  have eq47 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq12
  have eq101 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq14
  have eq293 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq14 eq25
  have eq295 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X0) ◇ X1) := superpose eq12 eq25
  have eq334 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((((X0 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq7 eq293
  have eq585 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))))) ◇ X0) := superpose eq29 eq14
  have eq853 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (((((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X1 ◇ X0)) := superpose eq25 eq295
  have eq908 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq334 eq853
  have eq909 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq908
  have eq910 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq909 eq101
  have eq1077 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = (((X3 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1)))) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1)))) ◇ (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)))) ◇ X1) := superpose eq910 eq28
  have eq1082 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1))) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1))))) ◇ (X0 ◇ X1)) := superpose eq910 eq47
  have eq1242 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq910 eq585
  have eq1286 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq910 eq909
  have eq1406 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = (((X3 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1)))) ◇ (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq910 eq1077
  have eq1407 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X3 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq910 eq1406
  have eq1413 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1))) = (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) := superpose eq910 eq1082
  have eq1414 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ X1)) = (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq910 eq1413
  have eq1735 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = ((X1 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq910 eq1242
  have eq1736 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq1414 eq1735
  have eq1815 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq1286 eq910
  have eq1817 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq1815 eq1736
  have eq1824 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X3 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq1815 eq1407
  have eq1970 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq1815 eq1817
  have eq1971 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1815 eq1970
  have eq1977 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq1971 eq1824
  have eq1978 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ X0) = X1 := superpose eq1815 eq1977
  have eq1979 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = X1 := superpose eq1815 eq1978
  have eq1980 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq1815 eq1979
  have eq1981 (X0 X3 : G) : X0 = X3 := superpose eq1980 eq1980
  have eq1983 (X0 : G) : sK0 ≠ X0 := superpose eq1981 eq8
  subsumption eq1983 eq1981


@[equational_result]
theorem Equation21720_implies_Equation2 (G : Type*) [Magma G] (h : Equation21720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X0))) = ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X0) := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3))) := superpose eq7 eq9
  have eq31 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq32 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose eq10 eq9
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (((X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq9
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq25 eq33
  have eq40 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq39 eq31
  have eq50 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := superpose eq32 eq10
  have eq63 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq10 eq11
  have eq72 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq11 eq32
  have eq81 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) := superpose eq63 eq72
  have eq82 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq39 eq81
  have eq83 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq82 eq40
  have eq87 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq83
  have eq116 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq87 eq39
  have eq121 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq87 eq50
  have eq159 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq87 eq121
  have eq160 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq116 eq159
  have eq161 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq87 eq160
  have eq162 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq161 eq10
  have eq163 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq161 eq14
  have eq169 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq161 eq163
  have eq171 (X0 X3 : G) : X0 = X3 := superpose eq162 eq169
  have eq190 (X0 : G) : sK0 ≠ X0 := superpose eq171 eq8
  subsumption eq190 eq171


@[equational_result]
theorem Equation21721_implies_Equation2 (G : Type*) [Magma G] (h : Equation21721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ X3)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) := superpose eq7 eq11
  have eq30 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = ((((X4 ◇ (X4 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq7 eq22
  have eq32 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((((X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) ◇ X2) := superpose eq11 eq22
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3) := superpose eq22 eq30
  have eq48 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X2) := superpose eq22 eq32
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1) ◇ X2) := superpose eq46 eq48
  have eq50 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq11 eq49
  have eq89 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)))) := superpose eq22 eq9
  have eq126 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X1) := superpose eq50 eq50
  have eq195 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := superpose eq7 eq126
  have eq196 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = X0 := superpose eq195 eq11
  have eq200 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq196 eq7
  have eq204 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq196 eq13
  have eq220 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq200 eq89
  have eq222 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq220 eq200
  have eq230 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq222 eq204
  have eq231 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq220 eq230
  have eq232 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq231 eq196
  have eq240 (X0 X2 : G) : X0 = X2 := superpose eq232 eq232
  have eq245 (X0 : G) : sK0 ≠ X0 := superpose eq240 eq8
  subsumption eq245 eq240


@[equational_result]
theorem Equation21724_implies_Equation2 (G : Type*) [Magma G] (h : Equation21724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) ◇ X1)) ◇ X0) = X1 := superpose eq11 eq7
  have eq20 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq7 eq10
  have eq54 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) ◇ X1)) ◇ X1) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) ◇ X1)) ◇ (X0 ◇ X3))) = X0 := superpose eq11 eq9
  have eq62 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq20 eq9
  have eq81 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq62 eq10
  have eq82 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) ◇ X4))) := superpose eq62 eq9
  have eq103 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq81 eq11
  have eq104 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X1) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X0 ◇ X3))) = X0 := superpose eq81 eq54
  have eq105 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0) = X1 := superpose eq81 eq16
  have eq116 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) ◇ X4))) := superpose eq81 eq82
  have eq129 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq7 eq103
  have eq145 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0))) ◇ X0) = X1 := superpose eq129 eq105
  have eq146 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0))) ◇ X1) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X3))) = X0 := superpose eq129 eq104
  have eq156 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq129 eq116
  have eq208 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) = X1 := superpose eq129 eq145
  have eq209 (X0 X1 X3 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X3))) = X0 := superpose eq129 eq146
  have eq221 (X0 X2 X3 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) = (((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq129 eq156
  have eq222 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq129 eq221
  have eq223 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X3))) = X0 := superpose eq222 eq209
  have eq224 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq222 eq208
  have eq225 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq223 eq222
  have eq226 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq225 eq129
  have eq261 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq225 eq224
  have eq422 (X0 X1 : G) : X0 = X1 := superpose eq226 eq261
  have eq427 (X0 : G) : sK0 ≠ X0 := superpose eq422 eq8
  subsumption eq427 eq422


@[equational_result]
theorem Equation21727_implies_Equation2 (G : Type*) [Magma G] (h : Equation21727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X2) = ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0)) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X2) = ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3))) := superpose eq10 eq7
  have eq42 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X4) = (((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq9 eq10
  have eq49 (X0 X1 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X4) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq18 eq42
  have eq50 (X0 X1 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X4) = X1 := superpose eq10 eq49
  have eq54 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0)) = X2 := superpose eq50 eq12
  have eq78 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq50 eq54
  have eq107 (X0 X2 : G) : X0 = X2 := superpose eq78 eq78
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq112 eq107


@[equational_result]
theorem Equation21729_implies_Equation2 (G : Type*) [Magma G] (h : Equation21729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 X4 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4)) = X3 := superpose eq10 eq10
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))) := superpose eq7 eq9
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq9
  have eq68 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq7 eq35
  have eq75 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq15 eq35
  have eq92 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq35 eq15
  have eq140 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq75 eq24
  have eq149 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq92 eq140
  have eq151 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq149 eq68
  have eq177 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq149 eq151
  have eq178 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X4)) = X3 := superpose eq177 eq15
  have eq186 (X0 X3 : G) : ((X0 ◇ X0) ◇ X0) = X3 := superpose eq177 eq178
  have eq187 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq177 eq186
  have eq193 (X0 X2 : G) : X0 = X2 := superpose eq187 eq187
  have eq195 (X0 : G) : sK0 ≠ X0 := superpose eq193 eq8
  subsumption eq195 eq193


@[equational_result]
theorem Equation21730_implies_Equation2 (G : Type*) [Magma G] (h : Equation21730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X2)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X2)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq10 eq10
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X3 ◇ X3))) := superpose eq7 eq9
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ X1)) := superpose eq9 eq9
  have eq50 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := superpose eq10 eq35
  have eq65 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := superpose eq35 eq10
  have eq105 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq50 eq23
  have eq109 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq65 eq105
  have eq117 (X0 X1 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X3)) = X1 := superpose eq109 eq12
  have eq132 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq117 eq13
  have eq133 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) = X2 := superpose eq132 eq11
  have eq149 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X2 := superpose eq132 eq133
  have eq150 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq132 eq149
  have eq151 (X0 X3 : G) : X0 = X3 := superpose eq150 eq150
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq151 eq8
  subsumption eq153 eq151


@[equational_result]
theorem Equation21731_implies_Equation2 (G : Type*) [Magma G] (h : Equation21731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0) ◇ X3)) ◇ X2) = X3 := superpose eq11 eq11
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose eq10 eq11
  have eq26 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3)) = X2 := superpose eq11 eq10
  have eq41 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X0) := superpose eq11 eq23
  have eq76 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3)) = X2 := superpose eq41 eq26
  have eq78 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ X2) = X3 := superpose eq41 eq21
  have eq81 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X3)) = X2 := superpose eq41 eq76
  have eq84 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq81 eq78
  have eq123 (X0 X4 : G) : X0 = X4 := superpose eq7 eq84
  have eq199 (X0 : G) : sK0 ≠ X0 := superpose eq123 eq8
  subsumption eq199 eq123


@[equational_result]
theorem Equation21733_implies_Equation2 (G : Type*) [Magma G] (h : Equation21733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) := superpose eq7 eq12
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq12 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq19 eq15
  have eq27 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq20 eq12
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq20 eq19
  have eq40 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq30 eq27
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq40 eq40
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq53 eq48


@[equational_result]
theorem Equation21735_implies_Equation2 (G : Type*) [Magma G] (h : Equation21735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq15
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq108 eq41


@[equational_result]
theorem Equation21737_implies_Equation2 (G : Type*) [Magma G] (h : Equation21737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = X1 := superpose eq7 eq12
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ X0)) = X1 := superpose eq13 eq11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X1 := superpose eq13 eq20
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq12 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq49 eq31


@[equational_result]
theorem Equation21738_implies_Equation2 (G : Type*) [Magma G] (h : Equation21738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X2) = X3 := superpose eq12 eq12
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X0)) = X2 := superpose eq14 eq11
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq20 eq20
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq60 eq40


@[equational_result]
theorem Equation21739_implies_Equation2 (G : Type*) [Magma G] (h : Equation21739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X2 := superpose eq12 eq11
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq49 eq20


@[equational_result]
theorem Equation21741_implies_Equation2 (G : Type*) [Magma G] (h : Equation21741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = (X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))))) = X3 := superpose eq10 eq7
  have eq24 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))))) ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0))))) = X2 := superpose eq10 eq7
  have eq80 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq7 eq9
  have eq109 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X3) = (X0 ◇ ((X0 ◇ (X0 ◇ X4)) ◇ X4)) := superpose eq9 eq19
  have eq117 (X0 X1 X2 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X4) = X0 := superpose eq9 eq12
  have eq135 (X0 X4 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X4)) ◇ X4)) = X0 := superpose eq117 eq109
  have eq139 (X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = X2 := superpose eq135 eq19
  have eq159 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := superpose eq139 eq10
  have eq209 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) = X3 := superpose eq159 eq23
  have eq210 (X0 X2 X3 : G) : (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0))))) = X2 := superpose eq159 eq24
  have eq216 (X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = X1 := superpose eq210 eq9
  have eq228 (X0 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) = X3 := superpose eq216 eq11
  have eq236 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) = X1 := superpose eq216 eq80
  have eq247 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) = X3 := superpose eq216 eq209
  have eq249 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X3 := superpose eq216 eq228
  have eq255 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := superpose eq216 eq236
  have eq256 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq216 eq255
  have eq257 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq216 eq256
  have eq259 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq257 eq249
  have eq290 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq257 eq247
  have eq291 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq259 eq290
  have eq292 (X0 X3 : G) : X0 = X3 := superpose eq291 eq291
  have eq300 (X0 : G) : sK0 ≠ X0 := superpose eq292 eq8
  subsumption eq300 eq292


@[equational_result]
theorem Equation21742_implies_Equation2 (G : Type*) [Magma G] (h : Equation21742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := superpose eq11 eq11
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2)) := superpose eq7 eq11
  have eq21 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq14 eq15
  have eq22 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X2))) = X0 := superpose eq21 eq10
  have eq25 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq22 eq22
  have eq35 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq25
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = X0 := superpose eq35 eq7
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq35 eq36
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq45 eq45
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq48 eq46


@[equational_result]
theorem Equation21743_implies_Equation2 (G : Type*) [Magma G] (h : Equation21743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq12 eq12
  have eq25 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq17
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq128 eq42


@[equational_result]
theorem Equation21745_implies_Equation2 (G : Type*) [Magma G] (h : Equation21745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ (X0 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq12
  have eq16 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X4) = X3 := superpose eq12 eq12
  have eq25 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq13 eq16
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq180 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq180 eq61


@[equational_result]
theorem Equation21746_implies_Equation2 (G : Type*) [Magma G] (h : Equation21746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq15
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq168 eq60


@[equational_result]
theorem Equation21747_implies_Equation2 (G : Type*) [Magma G] (h : Equation21747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq15
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq119 eq54


@[equational_result]
theorem Equation21748_implies_Equation2 (G : Type*) [Magma G] (h : Equation21748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq15
  have eq56 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq122 eq56


@[equational_result]
theorem Equation21751_implies_Equation2 (G : Type*) [Magma G] (h : Equation21751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq11
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq12 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq12 eq13
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq16
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq16
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation21754_implies_Equation2 (G : Type*) [Magma G] (h : Equation21754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq34 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq13 eq12
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq34 eq34
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq104 eq52


@[equational_result]
theorem Equation21756_implies_Equation2 (G : Type*) [Magma G] (h : Equation21756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq25 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq11
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq25 eq25
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq102 eq44


@[equational_result]
theorem Equation21757_implies_Equation2 (G : Type*) [Magma G] (h : Equation21757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = X1 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X2))) = X1 := superpose eq7 eq9
  have eq38 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X1 := superpose eq9 eq21
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq38
  have eq60 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq40 eq38
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq60 eq60
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq74 eq72


@[equational_result]
theorem Equation21758_implies_Equation2 (G : Type*) [Magma G] (h : Equation21758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq37 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq12
  have eq64 (X0 X2 : G) : X0 = X2 := superpose eq37 eq37
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq138 eq64


@[equational_result]
theorem Equation21761_implies_Equation2 (G : Type*) [Magma G] (h : Equation21761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) = X1 := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq12 eq7
  have eq24 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) = X1 := superpose eq12 eq16
  have eq25 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq12 eq24
  have eq63 (X0 X1 : G) : X0 = X1 := superpose eq7 eq25
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq127 eq63


@[equational_result]
theorem Equation21763_implies_Equation2 (G : Type*) [Magma G] (h : Equation21763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation21764_implies_Equation2 (G : Type*) [Magma G] (h : Equation21764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21766_implies_Equation2 (G : Type*) [Magma G] (h : Equation21766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21767_implies_Equation2 (G : Type*) [Magma G] (h : Equation21767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21768_implies_Equation2 (G : Type*) [Magma G] (h : Equation21768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21770_implies_Equation2 (G : Type*) [Magma G] (h : Equation21770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq42 eq18


@[equational_result]
theorem Equation21771_implies_Equation2 (G : Type*) [Magma G] (h : Equation21771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq11 eq9
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) := superpose eq7 eq11
  have eq17 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq11
  have eq23 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq15
  have eq31 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq12 eq12
  have eq34 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq31 eq23
  have eq37 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq34 eq11
  have eq51 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq34 eq37
  have eq52 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq34 eq51
  have eq53 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq52 eq17
  have eq56 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq34 eq53
  have eq58 (X0 X1 : G) : X0 = X1 := superpose eq52 eq56
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq78 eq58


@[equational_result]
theorem Equation21772_implies_Equation2 (G : Type*) [Magma G] (h : Equation21772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X3 := superpose eq7 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation21774_implies_Equation2 (G : Type*) [Magma G] (h : Equation21774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation21775_implies_Equation2 (G : Type*) [Magma G] (h : Equation21775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21776_implies_Equation2 (G : Type*) [Magma G] (h : Equation21776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21778_implies_Equation2 (G : Type*) [Magma G] (h : Equation21778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21779_implies_Equation2 (G : Type*) [Magma G] (h : Equation21779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21780_implies_Equation2 (G : Type*) [Magma G] (h : Equation21780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21782_implies_Equation2 (G : Type*) [Magma G] (h : Equation21782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21783_implies_Equation2 (G : Type*) [Magma G] (h : Equation21783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21784_implies_Equation2 (G : Type*) [Magma G] (h : Equation21784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21785_implies_Equation2 (G : Type*) [Magma G] (h : Equation21785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21787_implies_Equation2 (G : Type*) [Magma G] (h : Equation21787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq9
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq23 eq23
  have eq68 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq49 eq12
  have eq79 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X0)) := superpose eq68 eq11
  have eq80 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq68 eq7
  have eq91 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq68 eq79
  have eq92 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq68 eq91
  have eq93 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq68 eq80
  have eq94 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq93 eq92
  have eq105 (X0 X1 : G) : X0 = X1 := superpose eq93 eq94
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq115 eq105


@[equational_result]
theorem Equation21788_implies_Equation2 (G : Type*) [Magma G] (h : Equation21788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) = X2 := superpose eq7 eq7
  have eq34 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))))) = X2 := superpose eq7 eq10
  have eq37 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq10
  have eq50 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq37
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = X2 := superpose eq50 eq34
  have eq75 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq50 eq51
  have eq76 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq50 eq75
  have eq77 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq76 eq50
  have eq82 (X0 X1 : G) : X0 = X1 := superpose eq76 eq77
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq84 eq82


@[equational_result]
theorem Equation21789_implies_Equation2 (G : Type*) [Magma G] (h : Equation21789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq12
  have eq14 (X0 X1 X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = (X1 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X0)) := superpose eq13 eq11
  have eq17 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq13 eq14
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq13 eq17
  have eq22 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq19 eq17
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation21791_implies_Equation2 (G : Type*) [Magma G] (h : Equation21791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq11
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq11 eq7
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = ((((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq7 eq12
  have eq25 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := superpose eq12 eq12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq12 eq12
  have eq37 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) = ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq12 eq7
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq11 eq16
  have eq45 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq16 eq16
  have eq54 (X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq45 eq43
  have eq55 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq54 eq21
  have eq64 (X0 X3 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq55 eq25
  have eq71 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq55 eq64
  have eq91 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq10 eq7
  have eq97 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq91 eq23
  have eq122 (X0 X1 X3 : G) : (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X3)) := superpose eq12 eq30
  have eq141 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq30 eq7
  have eq164 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ X3)) := superpose eq55 eq122
  have eq169 (X0 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := superpose eq141 eq37
  have eq172 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := superpose eq169 eq164
  have eq174 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq169 eq71
  have eq179 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq172 eq7
  have eq182 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq172 eq97
  have eq196 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq174 eq179
  have eq197 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq174 eq182
  have eq205 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq197 eq196
  have eq229 (X0 X1 : G) : X0 = X1 := superpose eq205 eq197
  have eq231 (X0 : G) : sK0 ≠ X0 := superpose eq229 eq8
  subsumption eq231 eq229


@[equational_result]
theorem Equation21792_implies_Equation2 (G : Type*) [Magma G] (h : Equation21792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq11
  have eq51 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq34
  have eq56 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X1 := superpose eq51 eq11
  have eq73 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq51 eq56
  have eq102 (X0 X2 : G) : X0 = X2 := superpose eq73 eq73
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq104 eq102


@[equational_result]
theorem Equation21793_implies_Equation2 (G : Type*) [Magma G] (h : Equation21793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X4))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X2 := superpose eq12 eq7
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X4 := superpose eq12 eq7
  have eq45 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((X2 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq12 eq10
  have eq57 (X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = X2 := superpose eq25 eq45
  have eq69 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)) = X2 := superpose eq57 eq25
  have eq70 (X0 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X0))) = X4 := superpose eq57 eq26
  have eq78 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq57 eq69
  have eq79 (X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X4) = X4 := superpose eq78 eq70
  have eq80 (X2 X4 : G) : (X2 ◇ X4) = X4 := superpose eq57 eq79
  have eq81 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq80 eq78
  have eq92 (X0 X1 : G) : X0 = X1 := superpose eq80 eq81
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq94 eq92


@[equational_result]
theorem Equation21797_implies_Equation2 (G : Type*) [Magma G] (h : Equation21797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X3 := superpose eq12 eq7
  have eq49 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X2 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq12 eq10
  have eq64 (X3 X4 : G) : (X3 ◇ X4) = X3 := superpose eq25 eq49
  have eq65 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq64 eq7
  have eq92 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq64 eq65
  have eq93 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq64 eq92
  have eq112 (X0 X1 : G) : X0 = X1 := superpose eq93 eq64
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq112 eq8
  subsumption eq131 eq112


@[equational_result]
theorem Equation21799_implies_Equation2 (G : Type*) [Magma G] (h : Equation21799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X2 ◇ X4)) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq12
  have eq128 (X0 X3 : G) : X0 = X3 := superpose eq45 eq45
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq128 eq8
  subsumption eq169 eq128


@[equational_result]
theorem Equation21800_implies_Equation2 (G : Type*) [Magma G] (h : Equation21800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ X3)) = ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) := superpose eq7 eq7
  have eq107 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq12
  have eq167 (X0 X3 : G) : X0 = X3 := superpose eq107 eq107
  have eq317 (X0 : G) : sK0 ≠ X0 := superpose eq167 eq8
  subsumption eq317 eq167


@[equational_result]
theorem Equation21801_implies_Equation2 (G : Type*) [Magma G] (h : Equation21801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X4 ◇ (X5 ◇ X5))) = X4 := superpose eq7 eq7
  have eq29 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X5))) = X4 := superpose eq7 eq9
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq29
  have eq65 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq45 eq29
  have eq80 (X0 X3 : G) : X0 = X3 := superpose eq65 eq65
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq82 eq80


@[equational_result]
theorem Equation21802_implies_Equation2 (G : Type*) [Magma G] (h : Equation21802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = (X3 ◇ (X3 ◇ X4)) := superpose eq7 eq7
  have eq31 (X0 X5 X6 : G) : (X5 ◇ (X5 ◇ X6)) = X0 := superpose eq7 eq12
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq154 eq70


@[equational_result]
theorem Equation21804_implies_Equation2 (G : Type*) [Magma G] (h : Equation21804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = (((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X4)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq7 eq10
  have eq31 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) = (((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X5)) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X4)))) := superpose eq10 eq10
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq10 eq10
  have eq39 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X4) ◇ ((X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ (X5 ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))))) = X5 := superpose eq10 eq9
  have eq40 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X4)) ◇ ((X0 ◇ X3) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) = X0 := superpose eq10 eq7
  have eq69 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq35 eq7
  have eq96 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq69 eq17
  have eq98 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq69 eq96
  have eq102 (X0 X1 X3 X4 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X4)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq98 eq29
  have eq103 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) = (((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X5)) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq98 eq31
  have eq107 (X0 X1 X4 X5 : G) : (((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X4) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ (X5 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))))) = X5 := superpose eq98 eq39
  have eq108 (X0 X1 X3 X4 : G) : (((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X4)) ◇ ((X0 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) = X0 := superpose eq98 eq40
  have eq122 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq98 eq7
  have eq136 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X4)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)) := superpose eq98 eq102
  have eq137 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)) := superpose eq98 eq136
  have eq138 (X0 X2 X3 X5 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) = (((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ X5)) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq98 eq103
  have eq139 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) = ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq98 eq138
  have eq140 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3)) = (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) := superpose eq98 eq139
  have eq141 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X2) = (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) := superpose eq98 eq140
  have eq142 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq141 eq137
  have eq150 (X0 X1 X4 X5 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X4) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X5 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = X5 := superpose eq98 eq107
  have eq151 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X0 ◇ (X5 ◇ X0))) = X5 := superpose eq98 eq150
  have eq153 (X0 X1 X3 X4 : G) : (((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X4)) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq98 eq108
  have eq154 (X0 X1 X3 X4 : G) : (((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X1) = X0 := superpose eq151 eq153
  have eq155 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X1) = X0 := superpose eq98 eq154
  have eq156 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := superpose eq155 eq142
  have eq157 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq155 eq141
  have eq163 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq157 eq156
  have eq189 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq163 eq122
  have eq192 (X0 X2 : G) : X0 = X2 := superpose eq189 eq189
  have eq194 (X0 : G) : sK0 ≠ X0 := superpose eq192 eq8
  subsumption eq194 eq192


@[equational_result]
theorem Equation21805_implies_Equation2 (G : Type*) [Magma G] (h : Equation21805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2))) ◇ X0) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X4 ◇ X3))) = X4 := superpose eq10 eq7
  have eq44 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X3)))) = X1 := superpose eq11 eq11
  have eq63 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ X0) := superpose eq7 eq22
  have eq72 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X3) = ((X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq22 eq7
  have eq142 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X2))) ◇ X3) = X1 := superpose eq63 eq11
  have eq144 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X3 ◇ X2))) = X3 := superpose eq63 eq7
  have eq167 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := superpose eq63 eq7
  have eq186 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq144 eq142
  have eq197 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X4 ◇ X3))))) ◇ (X2 ◇ (X5 ◇ X4))) = X5 := superpose eq11 eq29
  have eq266 (X0 X2 X4 X5 : G) : ((X2 ◇ X0) ◇ (X2 ◇ (X5 ◇ X4))) = X5 := superpose eq167 eq197
  have eq267 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X3) = X0 := superpose eq266 eq72
  have eq291 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X3)))) = X1 := superpose eq267 eq44
  have eq375 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X1 := superpose eq267 eq291
  have eq376 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq267 eq375
  have eq405 (X0 X1 : G) : X0 = X1 := superpose eq376 eq186
  have eq410 (X0 : G) : sK0 ≠ X0 := superpose eq405 eq8
  subsumption eq410 eq405


@[equational_result]
theorem Equation21806_implies_Equation2 (G : Type*) [Magma G] (h : Equation21806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X0) = X1 := superpose eq7 eq7
  have eq45 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq61 eq45


@[equational_result]
theorem Equation21808_implies_Equation2 (G : Type*) [Magma G] (h : Equation21808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21809_implies_Equation2 (G : Type*) [Magma G] (h : Equation21809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation21810_implies_Equation2 (G : Type*) [Magma G] (h : Equation21810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21812_implies_Equation2 (G : Type*) [Magma G] (h : Equation21812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21813_implies_Equation2 (G : Type*) [Magma G] (h : Equation21813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21814_implies_Equation2 (G : Type*) [Magma G] (h : Equation21814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21816_implies_Equation2 (G : Type*) [Magma G] (h : Equation21816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21817_implies_Equation2 (G : Type*) [Magma G] (h : Equation21817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21818_implies_Equation2 (G : Type*) [Magma G] (h : Equation21818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21819_implies_Equation2 (G : Type*) [Magma G] (h : Equation21819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21821_implies_Equation2 (G : Type*) [Magma G] (h : Equation21821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X1)) = (((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X3 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)))) ◇ (X1 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq11
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))))) = X3 := superpose eq11 eq11
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ (X3 ◇ (X3 ◇ X0)))) = ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq11 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq7 eq9
  have eq88 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X2))) = X0 := superpose eq11 eq10
  have eq115 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X2))) = ((X2 ◇ X1) ◇ (((X3 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X3)) := superpose eq88 eq88
  have eq116 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq88 eq88
  have eq117 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = X1 := superpose eq10 eq88
  have eq139 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X2))) = ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq116 eq115
  have eq140 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X1) ◇ X2)))) = X1 := superpose eq139 eq117
  have eq298 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq16 eq11
  have eq338 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X0)))) := superpose eq16 eq140
  have eq366 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X2))) := superpose eq11 eq338
  have eq382 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = (((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X0) ◇ X1) := superpose eq7 eq298
  have eq397 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1) ◇ X0) := superpose eq298 eq31
  have eq398 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))))) = X2 := superpose eq298 eq19
  have eq434 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq382 eq397
  have eq675 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) = ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1))) := superpose eq13 eq12
  have eq676 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = (X0 ◇ (((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1))) ◇ X1)) := superpose eq13 eq10
  have eq746 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq366 eq675
  have eq747 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq434 eq746
  have eq748 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq7 eq747
  have eq749 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))))) = X2 := superpose eq748 eq398
  have eq750 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq748 eq434
  have eq765 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = (X0 ◇ (X0 ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X1))) := superpose eq382 eq676
  have eq766 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))))) := superpose eq750 eq765
  have eq767 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := superpose eq749 eq766
  have eq768 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq748 eq767
  have eq769 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq768 eq750
  have eq773 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq769 eq11
  have eq774 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)))) ◇ X2) = X3 := superpose eq769 eq12
  have eq1277 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq769 eq773
  have eq1294 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq1277 eq774
  have eq1295 (X0 X3 : G) : X0 = X3 := superpose eq1294 eq1294
  have eq1300 (X0 : G) : sK0 ≠ X0 := superpose eq1295 eq8
  subsumption eq1300 eq1295


@[equational_result]
theorem Equation21822_implies_Equation2 (G : Type*) [Magma G] (h : Equation21822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X3 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))))) = X3 := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X2)) = (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = ((X3 ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0))) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X4 ◇ (X4 ◇ X2)))) := superpose eq7 eq10
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := superpose eq10 eq10
  have eq45 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq7 eq32
  have eq69 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq32 eq7
  have eq73 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X3 ◇ X1))) ◇ ((X3 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := superpose eq32 eq7
  have eq158 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq69 eq69
  have eq180 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X0) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0))) ◇ X0) := superpose eq69 eq69
  have eq185 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) = X2 := superpose eq32 eq69
  have eq200 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = ((X3 ◇ (X3 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X4 ◇ (X4 ◇ X0)))) := superpose eq69 eq10
  have eq203 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = (((X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X4 ◇ (X4 ◇ X0))) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X4 ◇ (X4 ◇ X0)))) := superpose eq69 eq17
  have eq205 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq69 eq32
  have eq207 (X0 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X0) = (X0 ◇ X0) := superpose eq185 eq180
  have eq212 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq207 eq158
  have eq214 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X2))) = X2 := superpose eq207 eq185
  have eq231 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) := superpose eq73 eq200
  have eq233 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq231 eq212
  have eq239 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = (((X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X4 ◇ (X4 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X4 ◇ (X4 ◇ X0)))) := superpose eq207 eq203
  have eq240 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = (((X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X4 ◇ (X4 ◇ X0))) ◇ (X4 ◇ (X4 ◇ X0))) := superpose eq233 eq239
  have eq241 (X0 X1 X2 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = (((X2 ◇ (X2 ◇ X0)) ◇ (X4 ◇ (X4 ◇ X0))) ◇ (X4 ◇ (X4 ◇ X0))) := superpose eq231 eq240
  have eq242 (X0 X1 X2 X4 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = (X0 ◇ (X4 ◇ (X4 ◇ X0))) := superpose eq69 eq241
  have eq300 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq32 eq214
  have eq337 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X0 := superpose eq300 eq242
  have eq338 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq337 eq205
  have eq340 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq338 eq207
  have eq342 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X2 := superpose eq340 eq214
  have eq371 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = ((X3 ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0))) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2)) := superpose eq342 eq28
  have eq379 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq342 eq45
  have eq491 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2)) := superpose eq342 eq371
  have eq492 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X2 := superpose eq342 eq491
  have eq504 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq492 eq379
  have eq505 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))))) = X3 := superpose eq504 eq13
  have eq538 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) = X3 := superpose eq504 eq505
  have eq539 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq504 eq538
  have eq540 (X0 X3 : G) : X0 = X3 := superpose eq539 eq539
  have eq542 (X0 : G) : sK0 ≠ X0 := superpose eq540 eq8
  subsumption eq542 eq540


@[equational_result]
theorem Equation21823_implies_Equation2 (G : Type*) [Magma G] (h : Equation21823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq61 eq18


@[equational_result]
theorem Equation21825_implies_Equation2 (G : Type*) [Magma G] (h : Equation21825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21826_implies_Equation2 (G : Type*) [Magma G] (h : Equation21826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation21827_implies_Equation2 (G : Type*) [Magma G] (h : Equation21827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21829_implies_Equation2 (G : Type*) [Magma G] (h : Equation21829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21830_implies_Equation2 (G : Type*) [Magma G] (h : Equation21830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21831_implies_Equation2 (G : Type*) [Magma G] (h : Equation21831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21833_implies_Equation2 (G : Type*) [Magma G] (h : Equation21833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21834_implies_Equation2 (G : Type*) [Magma G] (h : Equation21834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21835_implies_Equation2 (G : Type*) [Magma G] (h : Equation21835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21836_implies_Equation2 (G : Type*) [Magma G] (h : Equation21836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21838_implies_Equation2 (G : Type*) [Magma G] (h : Equation21838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X1 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X3 := superpose eq10 eq10
  have eq25 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq14 eq10
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation21839_implies_Equation2 (G : Type*) [Magma G] (h : Equation21839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq10 eq10
  have eq25 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq14 eq10
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq7 eq25
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq40 eq28


@[equational_result]
theorem Equation21840_implies_Equation2 (G : Type*) [Magma G] (h : Equation21840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X3))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq133 eq53


@[equational_result]
theorem Equation21841_implies_Equation2 (G : Type*) [Magma G] (h : Equation21841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X5 := superpose eq7 eq7
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation21843_implies_Equation2 (G : Type*) [Magma G] (h : Equation21843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21844_implies_Equation2 (G : Type*) [Magma G] (h : Equation21844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21845_implies_Equation2 (G : Type*) [Magma G] (h : Equation21845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21846_implies_Equation2 (G : Type*) [Magma G] (h : Equation21846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21848_implies_Equation2 (G : Type*) [Magma G] (h : Equation21848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21849_implies_Equation2 (G : Type*) [Magma G] (h : Equation21849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21850_implies_Equation2 (G : Type*) [Magma G] (h : Equation21850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21851_implies_Equation2 (G : Type*) [Magma G] (h : Equation21851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21853_implies_Equation2 (G : Type*) [Magma G] (h : Equation21853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21854_implies_Equation2 (G : Type*) [Magma G] (h : Equation21854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21855_implies_Equation2 (G : Type*) [Magma G] (h : Equation21855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21856_implies_Equation2 (G : Type*) [Magma G] (h : Equation21856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21858_implies_Equation2 (G : Type*) [Magma G] (h : Equation21858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21859_implies_Equation2 (G : Type*) [Magma G] (h : Equation21859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21860_implies_Equation2 (G : Type*) [Magma G] (h : Equation21860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21861_implies_Equation2 (G : Type*) [Magma G] (h : Equation21861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21862_implies_Equation2 (G : Type*) [Magma G] (h : Equation21862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21868_implies_Equation2 (G : Type*) [Magma G] (h : Equation21868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq16 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq11
  have eq17 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) := superpose eq11 eq7
  have eq33 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq9
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq11
  have eq58 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq16 eq10
  have eq68 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq22 eq58
  have eq73 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq68 eq11
  have eq77 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq68 eq17
  have eq87 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq73 eq33
  have eq90 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq68 eq77
  have eq92 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq90 eq87
  have eq96 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq92 eq7
  have eq98 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))))) = X1 := superpose eq92 eq10
  have eq99 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X0) := superpose eq92 eq12
  have eq105 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq92 eq34
  have eq122 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq92 eq98
  have eq130 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq92 eq105
  have eq131 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq92 eq130
  have eq132 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq131 eq99
  have eq187 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq92 eq96
  have eq191 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq132 eq187
  have eq193 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq132 eq132
  have eq198 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq191 eq193
  have eq201 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq198 eq122
  have eq218 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq198 eq201
  have eq219 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq198 eq218
  have eq227 (X0 X2 : G) : X0 = X2 := superpose eq219 eq219
  have eq235 (X0 : G) : sK0 ≠ X0 := superpose eq227 eq8
  subsumption eq235 eq227


@[equational_result]
theorem Equation21870_implies_Equation2 (G : Type*) [Magma G] (h : Equation21870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X2 ◇ X4)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X4)) ◇ (X1 ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = (X0 ◇ ((X1 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X4))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X0)) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq20 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq11
  have eq38 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (X4 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) := superpose eq10 eq10
  have eq49 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X6)))) ◇ (X7 ◇ X5)) ◇ (X0 ◇ X1)) = X5 := superpose eq10 eq11
  have eq52 (X0 X1 X2 X5 X7 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X7 ◇ X5)) ◇ (X0 ◇ X1)) = X5 := superpose eq38 eq49
  have eq54 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq11 eq20
  have eq56 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq20 eq20
  have eq71 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X0)) = X1 := superpose eq56 eq54
  have eq72 (X0 X1 X2 X4 : G) : (X0 ◇ (X2 ◇ X4)) = ((X1 ◇ X0) ◇ X4) := superpose eq71 eq9
  have eq77 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X1)) = X5 := superpose eq71 eq52
  have eq89 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X3 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq20 eq72
  have eq101 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := superpose eq20 eq72
  have eq125 (X0 X2 X3 : G) : (X2 ◇ X0) = (X2 ◇ (X3 ◇ X0)) := superpose eq101 eq12
  have eq136 (X0 X1 X2 X4 : G) : ((X2 ◇ X1) ◇ (X4 ◇ X0)) = X1 := superpose eq125 eq71
  have eq156 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq136 eq89
  have eq161 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq156 eq77
  have eq175 (X0 X3 : G) : X0 = X3 := superpose eq161 eq161
  have eq180 (X0 : G) : sK0 ≠ X0 := superpose eq175 eq8
  subsumption eq180 eq175


@[equational_result]
theorem Equation21872_implies_Equation2 (G : Type*) [Magma G] (h : Equation21872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = ((X0 ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0)))) := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq7 eq11
  have eq37 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X2 ◇ X1)))) ◇ X0) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq11 eq11
  have eq49 (X0 X3 : G) : (X0 ◇ X3) = (((X0 ◇ X3) ◇ X0) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq7 eq37
  have eq51 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq10 eq49
  have eq65 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3)) ◇ (X3 ◇ X2)) = X3 := superpose eq49 eq11
  have eq73 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X3 ◇ X2)) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X2))) := superpose eq7 eq12
  have eq106 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X0 ◇ X0) := superpose eq7 eq51
  have eq130 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X3 ◇ X2))) := superpose eq106 eq73
  have eq131 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = ((X0 ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X0 ◇ X0))) := superpose eq106 eq15
  have eq169 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X3 ◇ X2))) := superpose eq106 eq130
  have eq170 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = ((X0 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq106 eq131
  have eq171 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X2)) = X3 := superpose eq170 eq65
  have eq177 (X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X3 ◇ X2)) = X3 := superpose eq106 eq171
  have eq178 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq177 eq169
  have eq179 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X0) := superpose eq178 eq35
  have eq216 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq178 eq179
  have eq217 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq178 eq216
  have eq223 (X0 X1 : G) : X0 = X1 := superpose eq178 eq217
  have eq225 (X0 : G) : sK0 ≠ X0 := superpose eq223 eq8
  subsumption eq225 eq223


@[equational_result]
theorem Equation21873_implies_Equation2 (G : Type*) [Magma G] (h : Equation21873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq10
  have eq15 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq7
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq15
  have eq24 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) ◇ X0) := superpose eq11 eq7
  have eq36 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq13
  have eq47 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq20 eq36
  have eq48 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq47 eq24
  have eq51 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq47 eq48
  have eq52 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq51 eq32
  have eq55 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := superpose eq13 eq52
  have eq56 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq55 eq18
  have eq58 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq47 eq56
  have eq65 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq58 eq47
  have eq68 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq65 eq7
  have eq70 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq65 eq10
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X0 := superpose eq65 eq68
  have eq83 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq65 eq82
  have eq84 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq65 eq83
  have eq90 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = X2 := superpose eq65 eq70
  have eq91 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq65 eq90
  have eq124 (X0 X1 : G) : X0 = X1 := superpose eq84 eq91
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq124 eq8
  subsumption eq129 eq124


@[equational_result]
theorem Equation21874_implies_Equation2 (G : Type*) [Magma G] (h : Equation21874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X3) = (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X4 ◇ X5))) = X0 := superpose eq7 eq10
  have eq50 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq13 eq13
  have eq77 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq50 eq13
  have eq85 (X0 X2 : G) : X0 = X2 := superpose eq77 eq77
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq87 eq85


@[equational_result]
theorem Equation21876_implies_Equation2 (G : Type*) [Magma G] (h : Equation21876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X0 ◇ ((X3 ◇ X1) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = X1 := superpose eq11 eq11
  have eq26 (X0 X1 X2 X6 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X6 ◇ X1))) := superpose eq11 eq7
  have eq28 (X0 X1 X5 X6 X7 : G) : (X5 ◇ (X0 ◇ (X6 ◇ ((X0 ◇ X1) ◇ (X7 ◇ X5))))) = X0 := superpose eq11 eq10
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = ((X4 ◇ X2) ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X5 ◇ X0))) := superpose eq7 eq10
  have eq39 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq7 eq10
  have eq51 (X0 X1 X5 X6 : G) : (X5 ◇ (X0 ◇ (X6 ◇ (X1 ◇ X5)))) = X0 := superpose eq39 eq28
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq39 eq26
  have eq55 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = ((X4 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0)) := superpose eq39 eq33
  have eq69 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ X0))) := superpose eq39 eq55
  have eq70 (X0 X5 X6 : G) : (X5 ◇ (X6 ◇ X5)) = X0 := superpose eq69 eq51
  have eq72 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X1 := superpose eq69 eq20
  have eq73 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq72 eq52
  have eq82 (X0 X5 : G) : (X5 ◇ X5) = X0 := superpose eq73 eq70
  have eq87 (X0 X1 : G) : X0 = X1 := superpose eq73 eq82
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq92 eq87


@[equational_result]
theorem Equation21877_implies_Equation2 (G : Type*) [Magma G] (h : Equation21877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ X3)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X4 ◇ X3)) ◇ (X5 ◇ (X2 ◇ (X3 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = (X0 ◇ ((X3 ◇ X2) ◇ (X4 ◇ X0))) := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ (X5 ◇ X4))) = X0 := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X4 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) := superpose eq10 eq10
  have eq23 (X0 X1 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = ((X1 ◇ X0) ◇ (X4 ◇ X3)) := superpose eq18 eq9
  have eq24 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = (X0 ◇ (X2 ◇ (X4 ◇ X0))) := superpose eq23 eq10
  have eq26 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq13 eq24
  have eq27 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := superpose eq26 eq7
  have eq34 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X2)) = X0 := superpose eq26 eq27
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq26 eq34
  have eq36 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq26 eq35
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq36 eq26
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation21878_implies_Equation2 (G : Type*) [Magma G] (h : Equation21878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ X0))) = ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq15 (X0 X3 X4 : G) : (X3 ◇ X3) = (X0 ◇ ((X3 ◇ X3) ◇ X4)) := superpose eq7 eq11
  have eq16 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq11 eq11
  have eq25 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ (X0 ◇ X0))) = X0 := superpose eq16 eq12
  have eq29 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq16 eq25
  have eq30 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq29 eq15
  have eq34 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq29 eq30
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation21879_implies_Equation2 (G : Type*) [Magma G] (h : Equation21879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq11 eq11
  have eq26 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ X4)) ◇ X0) = X4 := superpose eq16 eq12
  have eq29 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq16 eq26
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation21881_implies_Equation2 (G : Type*) [Magma G] (h : Equation21881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) = (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X2 ◇ (X3 ◇ X0))))) := superpose eq7 eq9
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq7 eq9
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) = ((X0 ◇ X1) ◇ (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) := superpose eq7 eq10
  have eq29 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq10 eq10
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq9 eq10
  have eq44 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq16 eq10
  have eq53 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq7 eq44
  have eq78 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq16 eq11
  have eq100 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq78 eq9
  have eq109 (X0 X1 X2 X3 : G) : ((((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X3 ◇ X0)) ◇ (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq78 eq7
  have eq163 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq31 eq53
  have eq496 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = ((((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq78 eq100
  have eq502 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq78 eq100
  have eq503 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq7 eq100
  have eq555 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq100 eq10
  have eq575 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq109 eq496
  have eq585 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq502 eq575
  have eq601 (X0 X1 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq7 eq555
  have eq708 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = ((((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq78 eq503
  have eq713 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq100 eq503
  have eq718 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq503 eq11
  have eq730 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq503 eq7
  have eq762 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq502 eq708
  have eq763 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq585 eq762
  have eq764 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq585 eq713
  have eq770 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq764 eq763
  have eq796 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq770 eq601
  have eq880 (X0 X1 X3 : G) : ((X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq770
  have eq1036 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3)) = ((((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X0 ◇ X1))) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq27 eq12
  have eq1108 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq7 eq796
  have eq1109 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq16 eq796
  have eq1177 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq796 eq163
  have eq1183 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq770 eq1108
  have eq1184 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose eq880 eq1109
  have eq1296 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq718 eq770
  have eq1306 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq718 eq12
  have eq1321 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq770 eq1296
  have eq1361 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq1321 eq1184
  have eq1408 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq730 eq1306
  have eq1409 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq1408
  have eq1410 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq1321 eq1409
  have eq1424 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq1410 eq1177
  have eq1474 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq1410 eq1183
  have eq1538 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1361 eq1474
  have eq1552 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := superpose eq1538 eq796
  have eq1589 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq1538 eq1361
  have eq1592 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq1538 eq1424
  have eq1672 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq1538 eq1552
  have eq1709 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq1589 eq1592
  have eq1710 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq1538 eq1709
  have eq1711 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq1538 eq1710
  have eq1712 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1711 eq1672
  have eq1714 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq1712 eq29
  have eq1729 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3)) = (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq1712 eq1036
  have eq1941 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq1712 eq1714
  have eq1942 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := superpose eq1712 eq1941
  have eq1943 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := superpose eq1712 eq1942
  have eq1944 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X0 := superpose eq1712 eq1943
  have eq1945 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq1712 eq1944
  have eq1946 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1712 eq1945
  have eq1994 (X0 X1 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3)) = X0 := superpose eq1946 eq1729
  have eq1995 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq1712 eq1994
  have eq2008 (X0 X1 : G) : X0 = X1 := superpose eq1946 eq1995
  have eq2022 (X0 : G) : sK0 ≠ X0 := superpose eq2008 eq8
  subsumption eq2022 eq2008


@[equational_result]
theorem Equation21882_implies_Equation2 (G : Type*) [Magma G] (h : Equation21882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X0))))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X1 ◇ X3)) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X4 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X4 ◇ (X2 ◇ (X0 ◇ X3)))) := superpose eq7 eq13
  have eq17 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X4) ◇ (X5 ◇ (X1 ◇ X2))) = (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq13 eq13
  have eq18 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq13
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X1 ◇ X2))) = ((X5 ◇ X4) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := superpose eq13 eq13
  have eq40 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X1 := superpose eq18 eq17
  have eq41 (X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X1 ◇ X2))) = X1 := superpose eq40 eq26
  have eq45 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (X3 ◇ (X4 ◇ (X2 ◇ (X0 ◇ X3)))) := superpose eq41 eq15
  have eq46 (X0 X1 X3 : G) : (X3 ◇ X0) = (X1 ◇ X0) := superpose eq41 eq45
  have eq87 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq12 eq46
  have eq178 (X0 X3 : G) : X0 = X3 := superpose eq7 eq87
  have eq307 (X0 : G) : sK0 ≠ X0 := superpose eq178 eq8
  subsumption eq307 eq178


@[equational_result]
theorem Equation21883_implies_Equation2 (G : Type*) [Magma G] (h : Equation21883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X3 X5 : G) : (((X1 ◇ X0) ◇ (X5 ◇ X1)) ◇ X3) = X1 := superpose eq12 eq12
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X0)) ◇ (X5 ◇ X2)) ◇ X0) = X2 := superpose eq12 eq7
  have eq26 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq14 eq22
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq7 eq26
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq129 eq52


@[equational_result]
theorem Equation21885_implies_Equation2 (G : Type*) [Magma G] (h : Equation21885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq21 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq9
  have eq54 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq110 eq54


@[equational_result]
theorem Equation21887_implies_Equation2 (G : Type*) [Magma G] (h : Equation21887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X2 ◇ (X2 ◇ X4)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X5))) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq9
  have eq83 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq167 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq167 eq83


@[equational_result]
theorem Equation21889_implies_Equation2 (G : Type*) [Magma G] (h : Equation21889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) := superpose eq7 eq9
  have eq60 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq7 eq25
  have eq75 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq60 eq10
  have eq90 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := superpose eq60 eq7
  have eq178 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq90 eq90
  have eq180 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq178 eq75
  have eq182 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X0 := superpose eq180 eq90
  have eq226 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq180 eq182
  have eq227 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq180 eq226
  have eq249 (X0 X1 : G) : X0 = X1 := superpose eq227 eq180
  have eq251 (X0 : G) : sK0 ≠ X0 := superpose eq249 eq8
  subsumption eq251 eq249


@[equational_result]
theorem Equation21890_implies_Equation2 (G : Type*) [Magma G] (h : Equation21890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq37 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ (X1 ◇ X2)) = X4 := superpose eq11 eq11
  have eq82 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq37 eq12
  have eq91 (X0 X2 : G) : X0 = X2 := superpose eq7 eq82
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq91 eq8
  subsumption eq142 eq91


@[equational_result]
theorem Equation21891_implies_Equation2 (G : Type*) [Magma G] (h : Equation21891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X5)) ◇ X4) = X5 := superpose eq12 eq12
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X1 ◇ X0)) ◇ (X3 ◇ X5)) ◇ X0) = X5 := superpose eq12 eq7
  have eq27 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq14 eq22
  have eq86 (X0 X3 : G) : X0 = X3 := superpose eq7 eq27
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq121 eq86


@[equational_result]
theorem Equation21893_implies_Equation2 (G : Type*) [Magma G] (h : Equation21893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X2 ◇ (X4 ◇ X2)) = ((X1 ◇ X0) ◇ (X1 ◇ (X5 ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq32 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))) = X5 := superpose eq9 eq7
  have eq43 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0)))) ◇ (X5 ◇ X6)) ◇ (X4 ◇ X3)) = X6 := superpose eq9 eq12
  have eq61 (X0 X2 X3 X4 X5 X6 : G) : (((X2 ◇ X0) ◇ (X5 ◇ X6)) ◇ (X4 ◇ X3)) = X6 := superpose eq32 eq43
  have eq62 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq61 eq12
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq7 eq62
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq133 eq65


@[equational_result]
theorem Equation21894_implies_Equation2 (G : Type*) [Magma G] (h : Equation21894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X2) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X4 ◇ X1))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X5 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ X4)) ◇ (X6 ◇ X5))) = X0 := superpose eq7 eq10
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X5)) ◇ (X0 ◇ X1)) = X5 := superpose eq10 eq7
  have eq39 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq35 eq13
  have eq78 (X0 X2 : G) : X0 = X2 := superpose eq7 eq39
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq165 eq78


@[equational_result]
theorem Equation21895_implies_Equation2 (G : Type*) [Magma G] (h : Equation21895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X2 ◇ (X4 ◇ X4)) = ((X1 ◇ X0) ◇ (X1 ◇ (X5 ◇ X5))) := superpose eq7 eq7
  have eq43 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq9
  have eq71 (X0 X3 : G) : X0 = X3 := superpose eq7 eq43
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq176 eq71


@[equational_result]
theorem Equation21896_implies_Equation2 (G : Type*) [Magma G] (h : Equation21896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq26 (X0 X3 X4 X5 X6 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ (X3 ◇ X4)) = X6 := superpose eq7 eq12
  have eq42 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq26 eq12
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq7 eq42
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq129 eq51


@[equational_result]
theorem Equation21899_implies_Equation2 (G : Type*) [Magma G] (h : Equation21899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X0)))) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := superpose eq7 eq10
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))) := superpose eq10 eq7
  have eq17 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) = (X0 ◇ ((X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2))))))) := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq7 eq9
  have eq34 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) = (X0 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X1)) := superpose eq7 eq29
  have eq47 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq29 eq7
  have eq119 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ ((((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1)))))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1))))))))) := superpose eq9 eq13
  have eq173 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X2)) ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq11 eq16
  have eq197 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X2 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1))))))) := superpose eq16 eq13
  have eq215 (X0 X1 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) = ((X0 ◇ X1) ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq10 eq34
  have eq219 (X0 X1 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))))) = (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))))) := superpose eq29 eq34
  have eq220 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))))) = (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))))) := superpose eq34 eq34
  have eq249 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))))) := superpose eq7 eq219
  have eq250 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))))) := superpose eq7 eq220
  have eq251 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X2 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq250 eq197
  have eq252 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq250 eq119
  have eq340 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = ((X3 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X1) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq252 eq252
  have eq352 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq252 eq17
  have eq354 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))))) := superpose eq252 eq12
  have eq356 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq252 eq9
  have eq357 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq252 eq7
  have eq377 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq357 eq354
  have eq378 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq377 eq356
  have eq379 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq377 eq352
  have eq381 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X3 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose eq378 eq340
  have eq392 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq379 eq357
  have eq396 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X3 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq379 eq381
  have eq486 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X3 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq252 eq396
  have eq487 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))) = (X2 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X2)) := superpose eq486 eq173
  have eq491 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X1))) = (X2 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X2)) := superpose eq392 eq487
  have eq492 (X1 X2 : G) : (X2 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X2)) = X2 := superpose eq7 eq491
  have eq596 (X0 X1 : G) : (X0 ◇ ((((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose eq10 eq492
  have eq615 (X0 X1 : G) : (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))) = X0 := superpose eq492 eq7
  have eq656 (X0 X1 : G) : (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose eq379 eq615
  have eq657 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq252 eq656
  have eq659 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq657 eq47
  have eq663 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq657 eq251
  have eq666 (X0 X1 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))))) = X1 := superpose eq657 eq249
  have eq712 (X0 X1 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq657 eq666
  have eq713 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq663 eq712
  have eq714 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq657 eq713
  have eq719 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq714 eq659
  have eq730 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq719 eq215
  have eq735 (X0 X1 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) = X0 := superpose eq719 eq596
  have eq773 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq657 eq730
  have eq794 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq735 eq773
  have eq795 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq794 eq7
  have eq940 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq794 eq795
  have eq941 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq794 eq940
  have eq942 (X0 X3 : G) : X0 = X3 := superpose eq941 eq941
  have eq944 (X0 : G) : sK0 ≠ X0 := superpose eq942 eq8
  subsumption eq944 eq942


@[equational_result]
theorem Equation21900_implies_Equation2 (G : Type*) [Magma G] (h : Equation21900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ X3) = (X0 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose eq10 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X4)) = ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X5))) := superpose eq10 eq7
  have eq23 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X4)) = X1 := superpose eq19 eq22
  have eq25 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = X3 := superpose eq23 eq12
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X0) = X2 := superpose eq25 eq7
  have eq31 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X2 := superpose eq23 eq29
  have eq32 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq31 eq23
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq7 eq32
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq84 eq33


@[equational_result]
theorem Equation21903_implies_Equation2 (G : Type*) [Magma G] (h : Equation21903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq10 eq7
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X2 := superpose eq14 eq7
  have eq231 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ (X1 ◇ X2))))) = X1 := superpose eq52 eq7
  have eq312 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq7 eq18
  have eq409 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq18 eq312
  have eq411 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq312 eq312
  have eq415 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose eq312 eq7
  have eq450 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq411 eq415
  have eq469 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq450 eq409
  have eq470 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq450 eq411
  have eq490 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq470 eq52
  have eq527 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X1 := superpose eq490 eq231
  have eq535 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq527 eq469
  have eq554 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := superpose eq535 eq7
  have eq779 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq535 eq554
  have eq780 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq535 eq779
  have eq781 (X0 X3 : G) : X0 = X3 := superpose eq780 eq780
  have eq783 (X0 : G) : sK0 ≠ X0 := superpose eq781 eq8
  subsumption eq783 eq781


@[equational_result]
theorem Equation21904_implies_Equation2 (G : Type*) [Magma G] (h : Equation21904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) ◇ ((X4 ◇ X0) ◇ X5)) ◇ X3) = X5 := superpose eq12 eq12
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ (X2 ◇ X3)) = X4 := superpose eq7 eq12
  have eq24 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq15 eq14
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq161 eq65


@[equational_result]
theorem Equation21907_implies_Equation2 (G : Type*) [Magma G] (h : Equation21907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq10 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq7 eq11
  have eq30 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq19
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq30 eq11
  have eq35 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq30 eq12
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq30 eq16
  have eq40 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ X2) := superpose eq35 eq37
  have eq41 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq30 eq40
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq41 eq34
  have eq47 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq41 eq43
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq47 eq47
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq50 eq48


@[equational_result]
theorem Equation21908_implies_Equation2 (G : Type*) [Magma G] (h : Equation21908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ (X2 ◇ X4))) := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq173 eq58


@[equational_result]
theorem Equation21910_implies_Equation2 (G : Type*) [Magma G] (h : Equation21910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X0 ◇ (X2 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ (X4 ◇ X0)) = X5 := superpose eq7 eq7
  have eq58 (X0 X1 X6 : G) : (X0 ◇ X1) = X6 := superpose eq10 eq11
  have eq70 (X0 X4 : G) : X0 = X4 := superpose eq7 eq58
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq159 eq70


@[equational_result]
theorem Equation21911_implies_Equation2 (G : Type*) [Magma G] (h : Equation21911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = (X0 ◇ (X2 ◇ (X4 ◇ X2))) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq175 eq59


@[equational_result]
theorem Equation21912_implies_Equation2 (G : Type*) [Magma G] (h : Equation21912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X3) = (X0 ◇ (X2 ◇ (X4 ◇ X4))) := superpose eq7 eq7
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq58 (X0 X1 : G) : X0 = X1 := superpose eq7 eq22
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq143 eq58


@[equational_result]
theorem Equation21913_implies_Equation2 (G : Type*) [Magma G] (h : Equation21913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X3 ◇ X4) = (X0 ◇ (X2 ◇ (X5 ◇ X6))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq22
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq133 eq57


@[equational_result]
theorem Equation21915_implies_Equation2 (G : Type*) [Magma G] (h : Equation21915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X2 := superpose eq12 eq12
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X5 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0))))) = X2 := superpose eq12 eq7
  have eq25 (X0 X2 X3 X5 : G) : (X0 ◇ (X5 ◇ X3)) = X2 := superpose eq17 eq21
  have eq66 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq160 eq66


@[equational_result]
theorem Equation21916_implies_Equation2 (G : Type*) [Magma G] (h : Equation21916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq20 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq12 eq12
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq135 eq41


