import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation8663_implies_Equation2 (G : Type*) [Magma G] (h : Equation8663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8664_implies_Equation2 (G : Type*) [Magma G] (h : Equation8664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8668_implies_Equation2 (G : Type*) [Magma G] (h : Equation8668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation8670_implies_Equation2 (G : Type*) [Magma G] (h : Equation8670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8671_implies_Equation2 (G : Type*) [Magma G] (h : Equation8671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8672_implies_Equation2 (G : Type*) [Magma G] (h : Equation8672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8674_implies_Equation2 (G : Type*) [Magma G] (h : Equation8674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8675_implies_Equation2 (G : Type*) [Magma G] (h : Equation8675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8676_implies_Equation2 (G : Type*) [Magma G] (h : Equation8676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8678_implies_Equation2 (G : Type*) [Magma G] (h : Equation8678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8679_implies_Equation2 (G : Type*) [Magma G] (h : Equation8679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8680_implies_Equation2 (G : Type*) [Magma G] (h : Equation8680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8681_implies_Equation2 (G : Type*) [Magma G] (h : Equation8681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8683_implies_Equation2 (G : Type*) [Magma G] (h : Equation8683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ X0) ◇ (X2 ◇ X3))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq40 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ ((X6 ◇ X7) ◇ X1)) ◇ (X2 ◇ X3))) = ((X8 ◇ X9) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq10 eq10
  have eq41 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ X0)) ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq10
  have eq58 (X0 X1 X8 X9 : G) : ((X8 ◇ X9) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq41 eq40
  have eq78 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X4 := superpose eq10 eq58
  have eq164 (X0 X3 : G) : X0 = X3 := superpose eq78 eq78
  have eq327 (X0 : G) : sK0 ≠ X0 := superpose eq164 eq8
  subsumption eq327 eq164


@[equational_result]
theorem Equation8684_implies_Equation2 (G : Type*) [Magma G] (h : Equation8684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X5) ◇ X2))) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq9
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation8685_implies_Equation2 (G : Type*) [Magma G] (h : Equation8685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq7 eq11
  have eq18 (X0 X1 X2 X6 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) = X6 := superpose eq11 eq11
  have eq33 (X2 X6 : G) : (X2 ◇ X2) = X6 := superpose eq16 eq18
  have eq42 (X0 X2 : G) : X0 = X2 := superpose eq33 eq33
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq44 eq42


@[equational_result]
theorem Equation8686_implies_Equation2 (G : Type*) [Magma G] (h : Equation8686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ (X1 ◇ X0)) = X4 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq29 eq17


@[equational_result]
theorem Equation8688_implies_Equation2 (G : Type*) [Magma G] (h : Equation8688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8689_implies_Equation2 (G : Type*) [Magma G] (h : Equation8689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8690_implies_Equation2 (G : Type*) [Magma G] (h : Equation8690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8691_implies_Equation2 (G : Type*) [Magma G] (h : Equation8691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8693_implies_Equation2 (G : Type*) [Magma G] (h : Equation8693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8694_implies_Equation2 (G : Type*) [Magma G] (h : Equation8694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8695_implies_Equation2 (G : Type*) [Magma G] (h : Equation8695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8696_implies_Equation2 (G : Type*) [Magma G] (h : Equation8696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8698_implies_Equation2 (G : Type*) [Magma G] (h : Equation8698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8699_implies_Equation2 (G : Type*) [Magma G] (h : Equation8699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8700_implies_Equation2 (G : Type*) [Magma G] (h : Equation8700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8701_implies_Equation2 (G : Type*) [Magma G] (h : Equation8701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8703_implies_Equation2 (G : Type*) [Magma G] (h : Equation8703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8704_implies_Equation2 (G : Type*) [Magma G] (h : Equation8704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8705_implies_Equation2 (G : Type*) [Magma G] (h : Equation8705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8706_implies_Equation2 (G : Type*) [Magma G] (h : Equation8706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8707_implies_Equation2 (G : Type*) [Magma G] (h : Equation8707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8709_implies_Equation2 (G : Type*) [Magma G] (h : Equation8709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation8710_implies_Equation2 (G : Type*) [Magma G] (h : Equation8710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq65 eq14


@[equational_result]
theorem Equation8711_implies_Equation2 (G : Type*) [Magma G] (h : Equation8711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8713_implies_Equation2 (G : Type*) [Magma G] (h : Equation8713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq40 eq15


@[equational_result]
theorem Equation8715_implies_Equation2 (G : Type*) [Magma G] (h : Equation8715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation8718_implies_Equation2 (G : Type*) [Magma G] (h : Equation8718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) ◇ (X0 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq10
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq78 eq26


@[equational_result]
theorem Equation8719_implies_Equation2 (G : Type*) [Magma G] (h : Equation8719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8721_implies_Equation2 (G : Type*) [Magma G] (h : Equation8721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation8722_implies_Equation2 (G : Type*) [Magma G] (h : Equation8722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation8723_implies_Equation2 (G : Type*) [Magma G] (h : Equation8723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8724_implies_Equation2 (G : Type*) [Magma G] (h : Equation8724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8726_implies_Equation2 (G : Type*) [Magma G] (h : Equation8726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation8728_implies_Equation2 (G : Type*) [Magma G] (h : Equation8728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation8730_implies_Equation2 (G : Type*) [Magma G] (h : Equation8730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation8731_implies_Equation2 (G : Type*) [Magma G] (h : Equation8731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1)) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (((X0 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X1)) ◇ ((X4 ◇ X1) ◇ X1))) ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X1)) ◇ ((X4 ◇ X1) ◇ X1))) ◇ X2)) ◇ X0) ◇ X3)) = X4 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ (((X3 ◇ ((X0 ◇ ((X4 ◇ ((X5 ◇ X1) ◇ X1)) ◇ ((X5 ◇ X1) ◇ X1))) ◇ ((X4 ◇ ((X5 ◇ X1) ◇ X1)) ◇ ((X5 ◇ X1) ◇ X1)))) ◇ ((X0 ◇ ((X4 ◇ ((X5 ◇ X1) ◇ X1)) ◇ ((X5 ◇ X1) ◇ X1))) ◇ ((X4 ◇ ((X5 ◇ X1) ◇ X1)) ◇ ((X5 ◇ X1) ◇ X1)))) ◇ X2)) ◇ X3) ◇ X0) ◇ X4)) = X5 := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (((X4 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3)) ◇ X4) = ((X1 ◇ ((X0 ◇ ((X3 ◇ (((X4 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3)) ◇ X4)) ◇ X1)) ◇ (X5 ◇ ((X2 ◇ (X1 ◇ ((X0 ◇ ((X3 ◇ (((X4 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3)) ◇ X4)) ◇ X1))) ◇ X5))) := superpose eq10 eq9
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq9
  have eq40 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X1)) ◇ (X4 ◇ (((X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X1))) ◇ X4))) := superpose eq22 eq9
  have eq42 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ X3)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) := superpose eq22 eq7
  have eq265 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2))) ◇ (X4 ◇ (X1 ◇ X4))) = X1 := superpose eq42 eq22
  have eq270 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)))) = X1 := superpose eq42 eq7
  have eq610 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X1)))) := superpose eq22 eq270
  have eq662 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq610
  have eq749 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq662 eq10
  have eq787 (X0 X1 : G) : (X0 ◇ ((X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq662 eq749
  have eq1004 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ (((X1 ◇ ((X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2)))) ◇ ((X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2)))) ◇ X3)) := superpose eq14 eq7
  have eq1101 (X0 : G) : (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq662 eq787
  have eq1122 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (((X2 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X4)))) ◇ (X0 ◇ (X4 ◇ (X0 ◇ X4)))) ◇ X1)) ◇ X2) = ((X5 ◇ (((X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ X3)) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X4)))) ◇ (X0 ◇ (X4 ◇ (X0 ◇ X4)))) ◇ X1)) ◇ X2)) ◇ X5)) ◇ (X6 ◇ (((X4 ◇ (X0 ◇ X4)) ◇ (X5 ◇ (((X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ X3)) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X4)))) ◇ (X0 ◇ (X4 ◇ (X0 ◇ X4)))) ◇ X1)) ◇ X2)) ◇ X5))) ◇ X6))) := superpose eq22 eq18
  have eq1307 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ ((X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq1101 eq13
  have eq1311 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq1101 eq1307
  have eq1372 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq40
  have eq1537 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) = X1 := superpose eq1004 eq14
  have eq1539 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X2 := superpose eq1004 eq13
  have eq1581 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = ((((X3 ◇ X0) ◇ X3) ◇ X3) ◇ X2) := superpose eq1537 eq1537
  have eq1587 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) = (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq1311 eq1537
  have eq1597 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (X1 ◇ (((X0 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2))) ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2))) ◇ X1)) := superpose eq22 eq1537
  have eq1693 (X0 X2 : G) : (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq1537 eq1587
  have eq1720 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (X1 ◇ ((X0 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2))) ◇ X1)) := superpose eq7 eq1597
  have eq1721 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq1720
  have eq2067 (X0 X1 X2 : G) : (X0 ◇ (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0)) = X2 := superpose eq1721 eq1539
  have eq2094 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ X0) = X2 := superpose eq1539 eq1537
  have eq2148 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq2094 eq7
  have eq2533 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq2148 eq1372
  have eq2549 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq1693 eq2533
  have eq2563 (X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X2))) ◇ (X4 ◇ (X1 ◇ X4))) = X1 := superpose eq2549 eq265
  have eq2567 (X0 X1 X2 X3 X5 X6 : G) : ((X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2) = ((X5 ◇ (((X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ X3)) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2)) ◇ X5)) ◇ (X6 ◇ ((X0 ◇ (X5 ◇ (((X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ X3)) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2)) ◇ X5))) ◇ X6))) := superpose eq2549 eq1122
  have eq2938 (X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X1) = X1 := superpose eq2549 eq2563
  have eq2939 (X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X1) = X1 := superpose eq2549 eq2938
  have eq2940 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq2549 eq2939
  have eq2976 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2) = ((X5 ◇ (((X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ X3)) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2)) ◇ X5)) ◇ (X0 ◇ (X5 ◇ (((X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ X3)) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2)) ◇ X5)))) := superpose eq2549 eq2567
  have eq2977 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2) = X0 := superpose eq2549 eq2976
  have eq2978 (X0 X2 : G) : (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X2) = X0 := superpose eq2549 eq2977
  have eq2979 (X0 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq2940 eq2978
  have eq2984 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0)) = X2 := superpose eq2979 eq2067
  have eq2991 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq2549 eq2984
  have eq2992 (X0 X2 X3 : G) : ((((X3 ◇ X0) ◇ X3) ◇ X3) ◇ X2) = X2 := superpose eq2991 eq1581
  have eq2994 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq2992 eq1537
  have eq3053 (X0 X2 : G) : X0 = X2 := superpose eq2994 eq2994
  have eq3058 (X0 : G) : sK0 ≠ X0 := superpose eq3053 eq8
  subsumption eq3058 eq3053


@[equational_result]
theorem Equation8732_implies_Equation2 (G : Type*) [Magma G] (h : Equation8732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation8736_implies_Equation2 (G : Type*) [Magma G] (h : Equation8736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8738_implies_Equation2 (G : Type*) [Magma G] (h : Equation8738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq60 eq18


@[equational_result]
theorem Equation8739_implies_Equation2 (G : Type*) [Magma G] (h : Equation8739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq65 eq17


@[equational_result]
theorem Equation8740_implies_Equation2 (G : Type*) [Magma G] (h : Equation8740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation8741_implies_Equation2 (G : Type*) [Magma G] (h : Equation8741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8744_implies_Equation2 (G : Type*) [Magma G] (h : Equation8744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X3) ◇ (X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq9
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq78 eq26


@[equational_result]
theorem Equation8745_implies_Equation2 (G : Type*) [Magma G] (h : Equation8745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8749_implies_Equation2 (G : Type*) [Magma G] (h : Equation8749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8752_implies_Equation2 (G : Type*) [Magma G] (h : Equation8752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ ((X0 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2))) ◇ (X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq9
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq39 eq27


@[equational_result]
theorem Equation8753_implies_Equation2 (G : Type*) [Magma G] (h : Equation8753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8755_implies_Equation2 (G : Type*) [Magma G] (h : Equation8755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq56 eq19


@[equational_result]
theorem Equation8756_implies_Equation2 (G : Type*) [Magma G] (h : Equation8756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq71 eq19


@[equational_result]
theorem Equation8757_implies_Equation2 (G : Type*) [Magma G] (h : Equation8757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X4 ◇ (((X0 ◇ X4) ◇ X5) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq10
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq76 eq16


@[equational_result]
theorem Equation8758_implies_Equation2 (G : Type*) [Magma G] (h : Equation8758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8760_implies_Equation2 (G : Type*) [Magma G] (h : Equation8760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq47 eq30


@[equational_result]
theorem Equation8761_implies_Equation2 (G : Type*) [Magma G] (h : Equation8761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation8762_implies_Equation2 (G : Type*) [Magma G] (h : Equation8762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8763_implies_Equation2 (G : Type*) [Magma G] (h : Equation8763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8765_implies_Equation2 (G : Type*) [Magma G] (h : Equation8765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation8766_implies_Equation2 (G : Type*) [Magma G] (h : Equation8766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation8767_implies_Equation2 (G : Type*) [Magma G] (h : Equation8767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation8768_implies_Equation2 (G : Type*) [Magma G] (h : Equation8768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8770_implies_Equation2 (G : Type*) [Magma G] (h : Equation8770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq59 eq22


@[equational_result]
theorem Equation8771_implies_Equation2 (G : Type*) [Magma G] (h : Equation8771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq72 eq20


@[equational_result]
theorem Equation8772_implies_Equation2 (G : Type*) [Magma G] (h : Equation8772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X4 ◇ (((X0 ◇ X5) ◇ X4) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq29 eq16


@[equational_result]
theorem Equation8773_implies_Equation2 (G : Type*) [Magma G] (h : Equation8773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8775_implies_Equation2 (G : Type*) [Magma G] (h : Equation8775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq61 eq20


@[equational_result]
theorem Equation8776_implies_Equation2 (G : Type*) [Magma G] (h : Equation8776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation8777_implies_Equation2 (G : Type*) [Magma G] (h : Equation8777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8778_implies_Equation2 (G : Type*) [Magma G] (h : Equation8778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8780_implies_Equation2 (G : Type*) [Magma G] (h : Equation8780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation8781_implies_Equation2 (G : Type*) [Magma G] (h : Equation8781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation8782_implies_Equation2 (G : Type*) [Magma G] (h : Equation8782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8783_implies_Equation2 (G : Type*) [Magma G] (h : Equation8783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8784_implies_Equation2 (G : Type*) [Magma G] (h : Equation8784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8786_implies_Equation2 (G : Type*) [Magma G] (h : Equation8786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation8788_implies_Equation2 (G : Type*) [Magma G] (h : Equation8788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation8790_implies_Equation2 (G : Type*) [Magma G] (h : Equation8790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq69 eq16


@[equational_result]
theorem Equation8792_implies_Equation2 (G : Type*) [Magma G] (h : Equation8792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation8796_implies_Equation2 (G : Type*) [Magma G] (h : Equation8796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8798_implies_Equation2 (G : Type*) [Magma G] (h : Equation8798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation8799_implies_Equation2 (G : Type*) [Magma G] (h : Equation8799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq83 eq17


@[equational_result]
theorem Equation8800_implies_Equation2 (G : Type*) [Magma G] (h : Equation8800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq75 eq12


@[equational_result]
theorem Equation8801_implies_Equation2 (G : Type*) [Magma G] (h : Equation8801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8803_implies_Equation2 (G : Type*) [Magma G] (h : Equation8803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq62 eq16


@[equational_result]
theorem Equation8805_implies_Equation2 (G : Type*) [Magma G] (h : Equation8805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation8807_implies_Equation2 (G : Type*) [Magma G] (h : Equation8807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8808_implies_Equation2 (G : Type*) [Magma G] (h : Equation8808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8809_implies_Equation2 (G : Type*) [Magma G] (h : Equation8809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8811_implies_Equation2 (G : Type*) [Magma G] (h : Equation8811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8812_implies_Equation2 (G : Type*) [Magma G] (h : Equation8812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8813_implies_Equation2 (G : Type*) [Magma G] (h : Equation8813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8815_implies_Equation2 (G : Type*) [Magma G] (h : Equation8815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8816_implies_Equation2 (G : Type*) [Magma G] (h : Equation8816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8817_implies_Equation2 (G : Type*) [Magma G] (h : Equation8817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8818_implies_Equation2 (G : Type*) [Magma G] (h : Equation8818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X1) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8822_implies_Equation2 (G : Type*) [Magma G] (h : Equation8822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8824_implies_Equation2 (G : Type*) [Magma G] (h : Equation8824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8825_implies_Equation2 (G : Type*) [Magma G] (h : Equation8825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8826_implies_Equation2 (G : Type*) [Magma G] (h : Equation8826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8828_implies_Equation2 (G : Type*) [Magma G] (h : Equation8828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8829_implies_Equation2 (G : Type*) [Magma G] (h : Equation8829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8830_implies_Equation2 (G : Type*) [Magma G] (h : Equation8830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8832_implies_Equation2 (G : Type*) [Magma G] (h : Equation8832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8833_implies_Equation2 (G : Type*) [Magma G] (h : Equation8833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8834_implies_Equation2 (G : Type*) [Magma G] (h : Equation8834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8835_implies_Equation2 (G : Type*) [Magma G] (h : Equation8835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8837_implies_Equation2 (G : Type*) [Magma G] (h : Equation8837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq49 eq31


@[equational_result]
theorem Equation8838_implies_Equation2 (G : Type*) [Magma G] (h : Equation8838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X5) ◇ X2))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq9 eq9
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq171 eq68


@[equational_result]
theorem Equation8839_implies_Equation2 (G : Type*) [Magma G] (h : Equation8839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation8840_implies_Equation2 (G : Type*) [Magma G] (h : Equation8840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8842_implies_Equation2 (G : Type*) [Magma G] (h : Equation8842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8843_implies_Equation2 (G : Type*) [Magma G] (h : Equation8843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8844_implies_Equation2 (G : Type*) [Magma G] (h : Equation8844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8845_implies_Equation2 (G : Type*) [Magma G] (h : Equation8845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8847_implies_Equation2 (G : Type*) [Magma G] (h : Equation8847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8848_implies_Equation2 (G : Type*) [Magma G] (h : Equation8848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8849_implies_Equation2 (G : Type*) [Magma G] (h : Equation8849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8850_implies_Equation2 (G : Type*) [Magma G] (h : Equation8850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8852_implies_Equation2 (G : Type*) [Magma G] (h : Equation8852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8853_implies_Equation2 (G : Type*) [Magma G] (h : Equation8853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8854_implies_Equation2 (G : Type*) [Magma G] (h : Equation8854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8855_implies_Equation2 (G : Type*) [Magma G] (h : Equation8855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8857_implies_Equation2 (G : Type*) [Magma G] (h : Equation8857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8858_implies_Equation2 (G : Type*) [Magma G] (h : Equation8858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8859_implies_Equation2 (G : Type*) [Magma G] (h : Equation8859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8860_implies_Equation2 (G : Type*) [Magma G] (h : Equation8860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8861_implies_Equation2 (G : Type*) [Magma G] (h : Equation8861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X1 ◇ X3) ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8864_implies_Equation2 (G : Type*) [Magma G] (h : Equation8864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X2 ◇ X0) ◇ X0) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq77 eq26


@[equational_result]
theorem Equation8865_implies_Equation2 (G : Type*) [Magma G] (h : Equation8865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8869_implies_Equation2 (G : Type*) [Magma G] (h : Equation8869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8872_implies_Equation2 (G : Type*) [Magma G] (h : Equation8872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ (X0 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq10
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq78 eq26


@[equational_result]
theorem Equation8873_implies_Equation2 (G : Type*) [Magma G] (h : Equation8873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8875_implies_Equation2 (G : Type*) [Magma G] (h : Equation8875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq56 eq19


@[equational_result]
theorem Equation8876_implies_Equation2 (G : Type*) [Magma G] (h : Equation8876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq70 eq18


@[equational_result]
theorem Equation8877_implies_Equation2 (G : Type*) [Magma G] (h : Equation8877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X4 ◇ (((X4 ◇ X0) ◇ X5) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq10
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq77 eq16


@[equational_result]
theorem Equation8878_implies_Equation2 (G : Type*) [Magma G] (h : Equation8878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8882_implies_Equation2 (G : Type*) [Magma G] (h : Equation8882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8884_implies_Equation2 (G : Type*) [Magma G] (h : Equation8884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8885_implies_Equation2 (G : Type*) [Magma G] (h : Equation8885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8886_implies_Equation2 (G : Type*) [Magma G] (h : Equation8886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8888_implies_Equation2 (G : Type*) [Magma G] (h : Equation8888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8889_implies_Equation2 (G : Type*) [Magma G] (h : Equation8889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8890_implies_Equation2 (G : Type*) [Magma G] (h : Equation8890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8892_implies_Equation2 (G : Type*) [Magma G] (h : Equation8892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8893_implies_Equation2 (G : Type*) [Magma G] (h : Equation8893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8894_implies_Equation2 (G : Type*) [Magma G] (h : Equation8894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8895_implies_Equation2 (G : Type*) [Magma G] (h : Equation8895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X1) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8898_implies_Equation2 (G : Type*) [Magma G] (h : Equation8898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X3) ◇ (X2 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq9
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq82 eq27


@[equational_result]
theorem Equation8899_implies_Equation2 (G : Type*) [Magma G] (h : Equation8899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8901_implies_Equation2 (G : Type*) [Magma G] (h : Equation8901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8902_implies_Equation2 (G : Type*) [Magma G] (h : Equation8902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8903_implies_Equation2 (G : Type*) [Magma G] (h : Equation8903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8905_implies_Equation2 (G : Type*) [Magma G] (h : Equation8905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8906_implies_Equation2 (G : Type*) [Magma G] (h : Equation8906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8907_implies_Equation2 (G : Type*) [Magma G] (h : Equation8907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8909_implies_Equation2 (G : Type*) [Magma G] (h : Equation8909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8910_implies_Equation2 (G : Type*) [Magma G] (h : Equation8910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8911_implies_Equation2 (G : Type*) [Magma G] (h : Equation8911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8912_implies_Equation2 (G : Type*) [Magma G] (h : Equation8912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X2) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8914_implies_Equation2 (G : Type*) [Magma G] (h : Equation8914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq35 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq12 eq12
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq35
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq159 eq42


@[equational_result]
theorem Equation8915_implies_Equation2 (G : Type*) [Magma G] (h : Equation8915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2)) ◇ X0)) = X5 := superpose eq7 eq7
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq57 eq39


@[equational_result]
theorem Equation8916_implies_Equation2 (G : Type*) [Magma G] (h : Equation8916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X5) ◇ (X3 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ X0)) = X5 := superpose eq7 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq29 eq16


@[equational_result]
theorem Equation8917_implies_Equation2 (G : Type*) [Magma G] (h : Equation8917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8919_implies_Equation2 (G : Type*) [Magma G] (h : Equation8919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8920_implies_Equation2 (G : Type*) [Magma G] (h : Equation8920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8921_implies_Equation2 (G : Type*) [Magma G] (h : Equation8921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8922_implies_Equation2 (G : Type*) [Magma G] (h : Equation8922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8924_implies_Equation2 (G : Type*) [Magma G] (h : Equation8924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8925_implies_Equation2 (G : Type*) [Magma G] (h : Equation8925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8926_implies_Equation2 (G : Type*) [Magma G] (h : Equation8926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8927_implies_Equation2 (G : Type*) [Magma G] (h : Equation8927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8929_implies_Equation2 (G : Type*) [Magma G] (h : Equation8929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8930_implies_Equation2 (G : Type*) [Magma G] (h : Equation8930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8931_implies_Equation2 (G : Type*) [Magma G] (h : Equation8931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8932_implies_Equation2 (G : Type*) [Magma G] (h : Equation8932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8934_implies_Equation2 (G : Type*) [Magma G] (h : Equation8934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8935_implies_Equation2 (G : Type*) [Magma G] (h : Equation8935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8936_implies_Equation2 (G : Type*) [Magma G] (h : Equation8936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8937_implies_Equation2 (G : Type*) [Magma G] (h : Equation8937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8938_implies_Equation2 (G : Type*) [Magma G] (h : Equation8938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8940_implies_Equation2 (G : Type*) [Magma G] (h : Equation8940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq67 eq20


@[equational_result]
theorem Equation8941_implies_Equation2 (G : Type*) [Magma G] (h : Equation8941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq65 eq14


@[equational_result]
theorem Equation8942_implies_Equation2 (G : Type*) [Magma G] (h : Equation8942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8943_implies_Equation2 (G : Type*) [Magma G] (h : Equation8943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8945_implies_Equation2 (G : Type*) [Magma G] (h : Equation8945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq81 eq20


@[equational_result]
theorem Equation8946_implies_Equation2 (G : Type*) [Magma G] (h : Equation8946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (((X5 ◇ X0) ◇ X3) ◇ X4)) = (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X3 ◇ (((X4 ◇ (X5 ◇ X2)) ◇ X6) ◇ X3)) = (X7 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X4) ◇ X1)) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X3 ◇ ((((X4 ◇ X2) ◇ X5) ◇ ((X6 ◇ X7) ◇ X3)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))))) = X7 := superpose eq9 eq7
  have eq41 (X0 X1 X2 X7 : G) : (X7 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) = X2 := superpose eq29 eq28
  have eq44 (X2 X3 X7 : G) : (X3 ◇ X2) = X7 := superpose eq41 eq34
  have eq81 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq193 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq193 eq81


@[equational_result]
theorem Equation8947_implies_Equation2 (G : Type*) [Magma G] (h : Equation8947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation8948_implies_Equation2 (G : Type*) [Magma G] (h : Equation8948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8950_implies_Equation2 (G : Type*) [Magma G] (h : Equation8950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ ((X3 ◇ X4) ◇ X5))) ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) ◇ X0) = X3 := superpose eq7 eq7
  have eq21 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ X5) ◇ X2))) = X5 := superpose eq12 eq12
  have eq25 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = X4 := superpose eq21 eq11
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq25 eq7
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq37 eq35


@[equational_result]
theorem Equation8951_implies_Equation2 (G : Type*) [Magma G] (h : Equation8951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ (((X3 ◇ X0) ◇ X2) ◇ X2)) ◇ (X0 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X2) ◇ X2))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ (((X3 ◇ X0) ◇ X2) ◇ X2)) ◇ X0)) = X5 := superpose eq7 eq10
  have eq26 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq81 eq26


@[equational_result]
theorem Equation8952_implies_Equation2 (G : Type*) [Magma G] (h : Equation8952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ X0)) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation8953_implies_Equation2 (G : Type*) [Magma G] (h : Equation8953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8955_implies_Equation2 (G : Type*) [Magma G] (h : Equation8955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq80 eq19


@[equational_result]
theorem Equation8956_implies_Equation2 (G : Type*) [Magma G] (h : Equation8956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation8957_implies_Equation2 (G : Type*) [Magma G] (h : Equation8957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8958_implies_Equation2 (G : Type*) [Magma G] (h : Equation8958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8960_implies_Equation2 (G : Type*) [Magma G] (h : Equation8960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq64 eq19


@[equational_result]
theorem Equation8961_implies_Equation2 (G : Type*) [Magma G] (h : Equation8961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation8962_implies_Equation2 (G : Type*) [Magma G] (h : Equation8962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8963_implies_Equation2 (G : Type*) [Magma G] (h : Equation8963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8964_implies_Equation2 (G : Type*) [Magma G] (h : Equation8964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8966_implies_Equation2 (G : Type*) [Magma G] (h : Equation8966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq83 eq20


@[equational_result]
theorem Equation8967_implies_Equation2 (G : Type*) [Magma G] (h : Equation8967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (((X5 ◇ (X3 ◇ X1)) ◇ X0) ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq58 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X2 := superpose eq10 eq7
  have eq99 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X3 := superpose eq58 eq58
  have eq109 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X0)) = X2 := superpose eq58 eq7
  have eq134 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq99 eq109
  have eq193 (X0 X4 : G) : X0 = X4 := superpose eq7 eq134
  have eq393 (X0 : G) : sK0 ≠ X0 := superpose eq193 eq8
  subsumption eq393 eq193


@[equational_result]
theorem Equation8968_implies_Equation2 (G : Type*) [Magma G] (h : Equation8968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation8969_implies_Equation2 (G : Type*) [Magma G] (h : Equation8969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8971_implies_Equation2 (G : Type*) [Magma G] (h : Equation8971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8972_implies_Equation2 (G : Type*) [Magma G] (h : Equation8972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8973_implies_Equation2 (G : Type*) [Magma G] (h : Equation8973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8974_implies_Equation2 (G : Type*) [Magma G] (h : Equation8974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8976_implies_Equation2 (G : Type*) [Magma G] (h : Equation8976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8977_implies_Equation2 (G : Type*) [Magma G] (h : Equation8977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8978_implies_Equation2 (G : Type*) [Magma G] (h : Equation8978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8979_implies_Equation2 (G : Type*) [Magma G] (h : Equation8979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8981_implies_Equation2 (G : Type*) [Magma G] (h : Equation8981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8982_implies_Equation2 (G : Type*) [Magma G] (h : Equation8982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8983_implies_Equation2 (G : Type*) [Magma G] (h : Equation8983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8984_implies_Equation2 (G : Type*) [Magma G] (h : Equation8984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8986_implies_Equation2 (G : Type*) [Magma G] (h : Equation8986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8987_implies_Equation2 (G : Type*) [Magma G] (h : Equation8987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8988_implies_Equation2 (G : Type*) [Magma G] (h : Equation8988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8989_implies_Equation2 (G : Type*) [Magma G] (h : Equation8989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8990_implies_Equation2 (G : Type*) [Magma G] (h : Equation8990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X1) ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8992_implies_Equation2 (G : Type*) [Magma G] (h : Equation8992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 X5 X6 : G) : ((X0 ◇ X4) ◇ X6) = X5 := superpose eq12 eq12
  have eq56 (X0 X5 : G) : X0 = X5 := superpose eq12 eq19
  have eq190 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq190 eq56


@[equational_result]
theorem Equation8993_implies_Equation2 (G : Type*) [Magma G] (h : Equation8993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ (((X3 ◇ X2) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X5) ◇ (X2 ◇ (((X3 ◇ X2) ◇ X0) ◇ X2))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ (((X3 ◇ X2) ◇ X0) ◇ X2)) ◇ X0)) = X5 := superpose eq7 eq9
  have eq27 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq85 eq27


@[equational_result]
theorem Equation8994_implies_Equation2 (G : Type*) [Magma G] (h : Equation8994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ X0)) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq73 eq15


@[equational_result]
theorem Equation8995_implies_Equation2 (G : Type*) [Magma G] (h : Equation8995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8997_implies_Equation2 (G : Type*) [Magma G] (h : Equation8997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8998_implies_Equation2 (G : Type*) [Magma G] (h : Equation8998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8999_implies_Equation2 (G : Type*) [Magma G] (h : Equation8999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9000_implies_Equation2 (G : Type*) [Magma G] (h : Equation9000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9002_implies_Equation2 (G : Type*) [Magma G] (h : Equation9002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9003_implies_Equation2 (G : Type*) [Magma G] (h : Equation9003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9004_implies_Equation2 (G : Type*) [Magma G] (h : Equation9004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9005_implies_Equation2 (G : Type*) [Magma G] (h : Equation9005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9007_implies_Equation2 (G : Type*) [Magma G] (h : Equation9007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9008_implies_Equation2 (G : Type*) [Magma G] (h : Equation9008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9009_implies_Equation2 (G : Type*) [Magma G] (h : Equation9009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9010_implies_Equation2 (G : Type*) [Magma G] (h : Equation9010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9012_implies_Equation2 (G : Type*) [Magma G] (h : Equation9012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9013_implies_Equation2 (G : Type*) [Magma G] (h : Equation9013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9014_implies_Equation2 (G : Type*) [Magma G] (h : Equation9014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9015_implies_Equation2 (G : Type*) [Magma G] (h : Equation9015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9016_implies_Equation2 (G : Type*) [Magma G] (h : Equation9016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X2) ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9018_implies_Equation2 (G : Type*) [Magma G] (h : Equation9018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation9019_implies_Equation2 (G : Type*) [Magma G] (h : Equation9019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9020_implies_Equation2 (G : Type*) [Magma G] (h : Equation9020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation9021_implies_Equation2 (G : Type*) [Magma G] (h : Equation9021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation9023_implies_Equation2 (G : Type*) [Magma G] (h : Equation9023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9024_implies_Equation2 (G : Type*) [Magma G] (h : Equation9024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9025_implies_Equation2 (G : Type*) [Magma G] (h : Equation9025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9026_implies_Equation2 (G : Type*) [Magma G] (h : Equation9026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9028_implies_Equation2 (G : Type*) [Magma G] (h : Equation9028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9029_implies_Equation2 (G : Type*) [Magma G] (h : Equation9029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9030_implies_Equation2 (G : Type*) [Magma G] (h : Equation9030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9031_implies_Equation2 (G : Type*) [Magma G] (h : Equation9031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9033_implies_Equation2 (G : Type*) [Magma G] (h : Equation9033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9034_implies_Equation2 (G : Type*) [Magma G] (h : Equation9034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9035_implies_Equation2 (G : Type*) [Magma G] (h : Equation9035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9036_implies_Equation2 (G : Type*) [Magma G] (h : Equation9036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9038_implies_Equation2 (G : Type*) [Magma G] (h : Equation9038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9039_implies_Equation2 (G : Type*) [Magma G] (h : Equation9039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9040_implies_Equation2 (G : Type*) [Magma G] (h : Equation9040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9041_implies_Equation2 (G : Type*) [Magma G] (h : Equation9041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9042_implies_Equation2 (G : Type*) [Magma G] (h : Equation9042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9044_implies_Equation2 (G : Type*) [Magma G] (h : Equation9044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X6 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0) = X6 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq53 eq35


@[equational_result]
theorem Equation9045_implies_Equation2 (G : Type*) [Magma G] (h : Equation9045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9046_implies_Equation2 (G : Type*) [Magma G] (h : Equation9046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation9047_implies_Equation2 (G : Type*) [Magma G] (h : Equation9047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation9048_implies_Equation2 (G : Type*) [Magma G] (h : Equation9048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X0) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation9050_implies_Equation2 (G : Type*) [Magma G] (h : Equation9050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9051_implies_Equation2 (G : Type*) [Magma G] (h : Equation9051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9052_implies_Equation2 (G : Type*) [Magma G] (h : Equation9052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9053_implies_Equation2 (G : Type*) [Magma G] (h : Equation9053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9054_implies_Equation2 (G : Type*) [Magma G] (h : Equation9054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X1) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9056_implies_Equation2 (G : Type*) [Magma G] (h : Equation9056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9057_implies_Equation2 (G : Type*) [Magma G] (h : Equation9057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9058_implies_Equation2 (G : Type*) [Magma G] (h : Equation9058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9059_implies_Equation2 (G : Type*) [Magma G] (h : Equation9059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9060_implies_Equation2 (G : Type*) [Magma G] (h : Equation9060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9062_implies_Equation2 (G : Type*) [Magma G] (h : Equation9062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9063_implies_Equation2 (G : Type*) [Magma G] (h : Equation9063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9064_implies_Equation2 (G : Type*) [Magma G] (h : Equation9064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9065_implies_Equation2 (G : Type*) [Magma G] (h : Equation9065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9066_implies_Equation2 (G : Type*) [Magma G] (h : Equation9066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X3) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9068_implies_Equation2 (G : Type*) [Magma G] (h : Equation9068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9069_implies_Equation2 (G : Type*) [Magma G] (h : Equation9069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9070_implies_Equation2 (G : Type*) [Magma G] (h : Equation9070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9071_implies_Equation2 (G : Type*) [Magma G] (h : Equation9071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9072_implies_Equation2 (G : Type*) [Magma G] (h : Equation9072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9074_implies_Equation2 (G : Type*) [Magma G] (h : Equation9074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X5) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9075_implies_Equation2 (G : Type*) [Magma G] (h : Equation9075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X5) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9076_implies_Equation2 (G : Type*) [Magma G] (h : Equation9076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X5) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9077_implies_Equation2 (G : Type*) [Magma G] (h : Equation9077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X5) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9078_implies_Equation2 (G : Type*) [Magma G] (h : Equation9078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X5) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9079_implies_Equation2 (G : Type*) [Magma G] (h : Equation9079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X5) ◇ X6))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9285_implies_Equation2 (G : Type*) [Magma G] (h : Equation9285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq7 eq10
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq16 eq11
  have eq22 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq7 eq21
  have eq33 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := superpose eq22 eq7
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq22 eq33
  have eq42 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq22 eq41
  have eq43 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq22 eq42
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq46 eq44


@[equational_result]
theorem Equation9288_implies_Equation2 (G : Type*) [Magma G] (h : Equation9288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) ◇ X0) = X1 := superpose eq7 eq10
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq9 eq23
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq9 eq32
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq93 eq35


@[equational_result]
theorem Equation9290_implies_Equation2 (G : Type*) [Magma G] (h : Equation9290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1)) := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq10 eq7
  have eq34 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq21
  have eq120 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq10 eq34
  have eq150 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq120 eq14
  have eq157 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq150 eq150
  have eq231 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq34 eq157
  have eq234 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq231 eq7
  have eq240 (X0 X1 : G) : X0 = X1 := superpose eq10 eq234
  have eq284 (X0 : G) : sK0 ≠ X0 := superpose eq240 eq8
  subsumption eq284 eq240


@[equational_result]
theorem Equation9291_implies_Equation2 (G : Type*) [Magma G] (h : Equation9291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq11
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq7 eq30
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq108 eq39


@[equational_result]
theorem Equation9292_implies_Equation2 (G : Type*) [Magma G] (h : Equation9292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq28
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq101 eq42


@[equational_result]
theorem Equation9295_implies_Equation2 (G : Type*) [Magma G] (h : Equation9295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq9
  have eq18 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq11 eq18
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq26 eq10
  have eq28 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq27
  have eq30 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq28 eq13
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq30 eq30
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq55 eq35


@[equational_result]
theorem Equation9298_implies_Equation2 (G : Type*) [Magma G] (h : Equation9298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq9
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq18 eq18
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq54 eq26


@[equational_result]
theorem Equation9300_implies_Equation2 (G : Type*) [Magma G] (h : Equation9300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq10 eq7
  have eq21 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq7
  have eq26 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq21 eq11
  have eq30 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq26 eq26
  have eq37 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq21
  have eq45 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq37 eq30
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := superpose eq45 eq7
  have eq55 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq45 eq26
  have eq69 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq45 eq55
  have eq73 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq69 eq49
  have eq83 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq73 eq73
  have eq84 (X0 X3 : G) : X0 = X3 := superpose eq73 eq83
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq91 eq84


@[equational_result]
theorem Equation9301_implies_Equation2 (G : Type*) [Magma G] (h : Equation9301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq30 eq12


@[equational_result]
theorem Equation9302_implies_Equation2 (G : Type*) [Magma G] (h : Equation9302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq37 eq13


@[equational_result]
theorem Equation9304_implies_Equation2 (G : Type*) [Magma G] (h : Equation9304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq11 eq7
  have eq28 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq9 eq11
  have eq30 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq28
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := superpose eq30 eq7
  have eq37 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq30 eq14
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq37 eq31
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq46 eq46
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq51 eq49


@[equational_result]
theorem Equation9305_implies_Equation2 (G : Type*) [Magma G] (h : Equation9305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X0))) = X2 := superpose eq12 eq10
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X0)) = X2 := superpose eq12 eq14
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation9306_implies_Equation2 (G : Type*) [Magma G] (h : Equation9306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9308_implies_Equation2 (G : Type*) [Magma G] (h : Equation9308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq35 eq13


@[equational_result]
theorem Equation9310_implies_Equation2 (G : Type*) [Magma G] (h : Equation9310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation9313_implies_Equation2 (G : Type*) [Magma G] (h : Equation9313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X3 ◇ X3))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) := superpose eq9 eq9
  have eq21 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq9
  have eq30 (X0 X1 X2 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) = X1 := superpose eq21 eq20
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X3) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X5 ◇ (X5 ◇ X5))) ◇ (X0 ◇ (X4 ◇ (X4 ◇ X4)))))) = X3 := superpose eq9 eq10
  have eq54 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq30 eq37
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq7 eq54
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq152 eq55


@[equational_result]
theorem Equation9314_implies_Equation2 (G : Type*) [Magma G] (h : Equation9314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9316_implies_Equation2 (G : Type*) [Magma G] (h : Equation9316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq40 eq15


@[equational_result]
theorem Equation9317_implies_Equation2 (G : Type*) [Magma G] (h : Equation9317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9318_implies_Equation2 (G : Type*) [Magma G] (h : Equation9318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9319_implies_Equation2 (G : Type*) [Magma G] (h : Equation9319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9322_implies_Equation2 (G : Type*) [Magma G] (h : Equation9322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq10
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq13
  have eq77 (X0 X3 : G) : X0 = X3 := superpose eq7 eq36
  have eq189 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq189 eq77


@[equational_result]
theorem Equation9325_implies_Equation2 (G : Type*) [Magma G] (h : Equation9325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq10
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq14
  have eq74 (X0 X3 : G) : X0 = X3 := superpose eq7 eq34
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq157 eq74


@[equational_result]
theorem Equation9327_implies_Equation2 (G : Type*) [Magma G] (h : Equation9327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) = ((X1 ◇ X0) ◇ ((((X0 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq7 eq11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1)) := superpose eq7 eq11
  have eq26 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X3 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0))))) = X1 := superpose eq11 eq9
  have eq28 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq9
  have eq32 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ X0)))))) ◇ ((X4 ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ X0))))))) ◇ (X4 ◇ X0))) = X4 := superpose eq9 eq7
  have eq36 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2))) := superpose eq11 eq14
  have eq116 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X0))) = X2 := superpose eq28 eq7
  have eq123 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq28 eq14
  have eq204 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ (X1 ◇ X3))))) := superpose eq123 eq14
  have eq490 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X4 ◇ X0)) ◇ X4)) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1)))) ◇ (X3 ◇ (X5 ◇ (((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X4 ◇ X0)) ◇ X4)))))) = X3 := superpose eq12 eq26
  have eq875 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ ((X4 ◇ (X0 ◇ X1)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X0)))) = X4 := superpose eq36 eq32
  have eq959 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ (X3 ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq875
  have eq983 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0)) := superpose eq875 eq7
  have eq1146 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq959
  have eq1321 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq1146
  have eq1538 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq116 eq1321
  have eq1707 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ (X1 ◇ X3))))) := superpose eq1538 eq204
  have eq1726 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X4 ◇ X0)) ◇ X4)) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1)))) ◇ (X3 ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X4 ◇ X0)) ◇ X4)))))) = X3 := superpose eq1538 eq490
  have eq1768 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq1538 eq983
  have eq2125 (X0 X1 X2 : G) : (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq1538 eq1707
  have eq2145 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X4 ◇ X0)) ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1)))) = X3 := superpose eq1538 eq1726
  have eq2146 (X0 X1 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X4 ◇ X0)) ◇ X4)) ◇ X1) = X3 := superpose eq1538 eq2145
  have eq2147 (X1 X3 X4 : G) : ((X1 ◇ X4) ◇ X1) = X3 := superpose eq2125 eq2146
  have eq2176 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq1538 eq1768
  have eq2183 (X1 X3 X4 : G) : (X4 ◇ X1) = X3 := superpose eq2176 eq2147
  have eq2185 (X0 X3 : G) : X0 = X3 := superpose eq2183 eq2183
  have eq2187 (X0 : G) : sK0 ≠ X0 := superpose eq2185 eq8
  subsumption eq2187 eq2185


@[equational_result]
theorem Equation9328_implies_Equation2 (G : Type*) [Magma G] (h : Equation9328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X0) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) = X2 := superpose eq10 eq7
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq13
  have eq83 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq15
  have eq104 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := superpose eq83 eq7
  have eq132 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq83 eq104
  have eq133 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq83 eq132
  have eq166 (X0 X1 : G) : X0 = X1 := superpose eq133 eq35
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq166 eq8
  subsumption eq177 eq166


@[equational_result]
theorem Equation9329_implies_Equation2 (G : Type*) [Magma G] (h : Equation9329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq107 eq30


@[equational_result]
theorem Equation9332_implies_Equation2 (G : Type*) [Magma G] (h : Equation9332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq10
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq14
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq173 eq70


@[equational_result]
theorem Equation9335_implies_Equation2 (G : Type*) [Magma G] (h : Equation9335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq13
  have eq75 (X0 X3 : G) : X0 = X3 := superpose eq7 eq35
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq183 eq75


@[equational_result]
theorem Equation9339_implies_Equation2 (G : Type*) [Magma G] (h : Equation9339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq107 eq30


@[equational_result]
theorem Equation9341_implies_Equation2 (G : Type*) [Magma G] (h : Equation9341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X3 ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq9 eq7
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq9 eq17
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq17
  have eq51 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq36 eq13
  have eq53 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq36 eq22
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq36 eq51
  have eq72 (X0 X2 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq71 eq35
  have eq73 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq36 eq72
  have eq74 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq73 eq36
  have eq81 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := superpose eq74 eq53
  have eq82 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq73 eq81
  have eq83 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq73 eq82
  have eq144 (X0 X2 : G) : X0 = X2 := superpose eq83 eq83
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq146 eq144


@[equational_result]
theorem Equation9342_implies_Equation2 (G : Type*) [Magma G] (h : Equation9342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq24 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq9 eq7
  have eq53 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq24
  have eq104 (X0 X3 : G) : X0 = X3 := superpose eq7 eq53
  have eq227 (X0 : G) : sK0 ≠ X0 := superpose eq104 eq8
  subsumption eq227 eq104


@[equational_result]
theorem Equation9343_implies_Equation2 (G : Type*) [Magma G] (h : Equation9343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9347_implies_Equation2 (G : Type*) [Magma G] (h : Equation9347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9350_implies_Equation2 (G : Type*) [Magma G] (h : Equation9350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) = ((X0 ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X1 ◇ (X4 ◇ (X4 ◇ X4)))) := superpose eq7 eq9
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X3 ◇ (X3 ◇ X3))) = ((X0 ◇ (X4 ◇ (X4 ◇ X4))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X5 ◇ (X5 ◇ X5)))) := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := superpose eq9 eq10
  have eq51 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq26 eq26
  have eq157 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := superpose eq10 eq51
  have eq159 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X4 ◇ (X4 ◇ X4)))) := superpose eq51 eq11
  have eq179 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq157 eq159
  have eq180 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0) = X1 := superpose eq179 eq9
  have eq182 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X4 ◇ X4))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X5 ◇ (X5 ◇ X5)))) = X1 := superpose eq179 eq11
  have eq273 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq179 eq180
  have eq277 (X0 X1 X2 X4 : G) : ((X0 ◇ (X4 ◇ (X4 ◇ X4))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2)))) = X1 := superpose eq179 eq182
  have eq278 (X0 X1 X4 : G) : ((X0 ◇ (X4 ◇ (X4 ◇ X4))) ◇ (X1 ◇ X0)) = X1 := superpose eq179 eq277
  have eq279 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq179 eq278
  have eq282 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq279 eq179
  have eq288 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq282 eq273
  have eq301 (X0 X2 : G) : X0 = X2 := superpose eq288 eq288
  have eq303 (X0 : G) : sK0 ≠ X0 := superpose eq301 eq8
  subsumption eq303 eq301


@[equational_result]
theorem Equation9351_implies_Equation2 (G : Type*) [Magma G] (h : Equation9351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation9353_implies_Equation2 (G : Type*) [Magma G] (h : Equation9353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0)) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq11 eq7
  have eq54 (X0 X5 : G) : X0 = X5 := superpose eq11 eq20
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq148 eq54


@[equational_result]
theorem Equation9354_implies_Equation2 (G : Type*) [Magma G] (h : Equation9354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9355_implies_Equation2 (G : Type*) [Magma G] (h : Equation9355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq39 eq12


@[equational_result]
theorem Equation9356_implies_Equation2 (G : Type*) [Magma G] (h : Equation9356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9358_implies_Equation2 (G : Type*) [Magma G] (h : Equation9358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9
  have eq49 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq16
  have eq68 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq49 eq7
  have eq91 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq49 eq68
  have eq92 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq49 eq91
  have eq93 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq49 eq92
  have eq186 (X0 X2 : G) : X0 = X2 := superpose eq93 eq93
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq186 eq8
  subsumption eq188 eq186


@[equational_result]
theorem Equation9359_implies_Equation2 (G : Type*) [Magma G] (h : Equation9359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq101 eq32


@[equational_result]
theorem Equation9360_implies_Equation2 (G : Type*) [Magma G] (h : Equation9360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq21 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq12 eq9
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq21 eq11
  have eq26 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq21 eq23
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq21 eq26
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation9362_implies_Equation2 (G : Type*) [Magma G] (h : Equation9362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9
  have eq77 (X0 X1 : G) : X0 = X1 := superpose eq10 eq14
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq112 eq77


@[equational_result]
theorem Equation9364_implies_Equation2 (G : Type*) [Magma G] (h : Equation9364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq72 eq44


@[equational_result]
theorem Equation9367_implies_Equation2 (G : Type*) [Magma G] (h : Equation9367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (((X0 ◇ X3) ◇ (X0 ◇ (X3 ◇ X3))) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X3 ◇ X3))))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq107 eq39


@[equational_result]
theorem Equation9368_implies_Equation2 (G : Type*) [Magma G] (h : Equation9368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq7 eq12
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation9370_implies_Equation2 (G : Type*) [Magma G] (h : Equation9370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X5 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq9 eq9
  have eq48 (X0 X5 : G) : X0 = X5 := superpose eq7 eq18
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq116 eq48


@[equational_result]
theorem Equation9371_implies_Equation2 (G : Type*) [Magma G] (h : Equation9371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq7 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq114 eq47


@[equational_result]
theorem Equation9372_implies_Equation2 (G : Type*) [Magma G] (h : Equation9372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X5 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq11 eq9
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq38 eq30


@[equational_result]
theorem Equation9373_implies_Equation2 (G : Type*) [Magma G] (h : Equation9373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X5 ◇ X1) = X0 := superpose eq7 eq12
  have eq45 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq107 eq45


@[equational_result]
theorem Equation9375_implies_Equation2 (G : Type*) [Magma G] (h : Equation9375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq9
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq9
  have eq76 (X0 X2 : G) : X0 = X2 := superpose eq13 eq42
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq102 eq76


@[equational_result]
theorem Equation9376_implies_Equation2 (G : Type*) [Magma G] (h : Equation9376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq42 eq15


@[equational_result]
theorem Equation9377_implies_Equation2 (G : Type*) [Magma G] (h : Equation9377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq38 eq30


@[equational_result]
theorem Equation9379_implies_Equation2 (G : Type*) [Magma G] (h : Equation9379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq23 eq13


@[equational_result]
theorem Equation9381_implies_Equation2 (G : Type*) [Magma G] (h : Equation9381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq12
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := superpose eq13 eq7
  have eq23 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X3))) = X0 := superpose eq13 eq18
  have eq24 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = X0 := superpose eq13 eq23
  have eq25 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq24
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation9385_implies_Equation2 (G : Type*) [Magma G] (h : Equation9385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (((X0 ◇ X3) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X3))) = X2 := superpose eq14 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq52 eq30


@[equational_result]
theorem Equation9387_implies_Equation2 (G : Type*) [Magma G] (h : Equation9387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X5 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq45 eq28


@[equational_result]
theorem Equation9388_implies_Equation2 (G : Type*) [Magma G] (h : Equation9388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation9389_implies_Equation2 (G : Type*) [Magma G] (h : Equation9389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq38 eq15


@[equational_result]
theorem Equation9390_implies_Equation2 (G : Type*) [Magma G] (h : Equation9390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq43 eq16


@[equational_result]
theorem Equation9393_implies_Equation2 (G : Type*) [Magma G] (h : Equation9393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation9394_implies_Equation2 (G : Type*) [Magma G] (h : Equation9394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9398_implies_Equation2 (G : Type*) [Magma G] (h : Equation9398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9401_implies_Equation2 (G : Type*) [Magma G] (h : Equation9401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X3) ◇ (X3 ◇ (X3 ◇ X3))) ◇ (((X0 ◇ X3) ◇ (X3 ◇ (X3 ◇ X3))) ◇ ((X0 ◇ X3) ◇ (X3 ◇ (X3 ◇ X3))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X3) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X0))) = X2 := superpose eq7 eq9
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq37 eq26


@[equational_result]
theorem Equation9402_implies_Equation2 (G : Type*) [Magma G] (h : Equation9402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X3) ◇ (X3 ◇ (X3 ◇ X4))) ◇ (((X0 ◇ X3) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X5)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X3))) = X2 := superpose eq14 eq9
  have eq32 (X0 X4 : G) : X0 = X4 := superpose eq21 eq21
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq50 eq32


@[equational_result]
theorem Equation9404_implies_Equation2 (G : Type*) [Magma G] (h : Equation9404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X3) ◇ (X3 ◇ (X4 ◇ X2))) ◇ (X5 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq12
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X2 := superpose eq13 eq9
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq48 eq26


@[equational_result]
theorem Equation9405_implies_Equation2 (G : Type*) [Magma G] (h : Equation9405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation9406_implies_Equation2 (G : Type*) [Magma G] (h : Equation9406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation9407_implies_Equation2 (G : Type*) [Magma G] (h : Equation9407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation9409_implies_Equation2 (G : Type*) [Magma G] (h : Equation9409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X2 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq7 eq7
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq9
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq28
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq105 eq35


@[equational_result]
theorem Equation9410_implies_Equation2 (G : Type*) [Magma G] (h : Equation9410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq48 eq12


@[equational_result]
theorem Equation9411_implies_Equation2 (G : Type*) [Magma G] (h : Equation9411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation9412_implies_Equation2 (G : Type*) [Magma G] (h : Equation9412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9414_implies_Equation2 (G : Type*) [Magma G] (h : Equation9414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation9415_implies_Equation2 (G : Type*) [Magma G] (h : Equation9415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X1))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ X0) := superpose eq11 eq7
  have eq49 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq7 eq22
  have eq152 (X0 X4 : G) : X0 = X4 := superpose eq7 eq49
  have eq265 (X0 : G) : sK0 ≠ X0 := superpose eq152 eq8
  subsumption eq265 eq152


@[equational_result]
theorem Equation9416_implies_Equation2 (G : Type*) [Magma G] (h : Equation9416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X4) ◇ (X5 ◇ (X1 ◇ X5))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X5 ◇ X0))) = X2 := superpose eq11 eq10
  have eq15 (X1 X2 X5 : G) : (X1 ◇ X5) = X2 := superpose eq11 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation9417_implies_Equation2 (G : Type*) [Magma G] (h : Equation9417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation9419_implies_Equation2 (G : Type*) [Magma G] (h : Equation9419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation9420_implies_Equation2 (G : Type*) [Magma G] (h : Equation9420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq53 eq14


@[equational_result]
theorem Equation9421_implies_Equation2 (G : Type*) [Magma G] (h : Equation9421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation9422_implies_Equation2 (G : Type*) [Magma G] (h : Equation9422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9424_implies_Equation2 (G : Type*) [Magma G] (h : Equation9424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X5 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq53 eq22


@[equational_result]
theorem Equation9425_implies_Equation2 (G : Type*) [Magma G] (h : Equation9425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation9426_implies_Equation2 (G : Type*) [Magma G] (h : Equation9426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (((X0 ◇ X4) ◇ (X5 ◇ (X5 ◇ X5))) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X2 := superpose eq11 eq10
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation9427_implies_Equation2 (G : Type*) [Magma G] (h : Equation9427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9429_implies_Equation2 (G : Type*) [Magma G] (h : Equation9429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq55 eq17


@[equational_result]
theorem Equation9430_implies_Equation2 (G : Type*) [Magma G] (h : Equation9430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation9431_implies_Equation2 (G : Type*) [Magma G] (h : Equation9431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation9432_implies_Equation2 (G : Type*) [Magma G] (h : Equation9432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9433_implies_Equation2 (G : Type*) [Magma G] (h : Equation9433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9436_implies_Equation2 (G : Type*) [Magma G] (h : Equation9436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq10
  have eq38 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq13
  have eq71 (X0 X3 : G) : X0 = X3 := superpose eq7 eq38
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq183 eq71


@[equational_result]
theorem Equation9439_implies_Equation2 (G : Type*) [Magma G] (h : Equation9439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq10
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq14
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq179 eq73


@[equational_result]
theorem Equation9441_implies_Equation2 (G : Type*) [Magma G] (h : Equation9441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X0) ◇ X2)) ◇ X1)) := superpose eq11 eq11
  have eq80 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq10 eq9
  have eq106 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X3) ◇ (X3 ◇ X1))) = X3 := superpose eq80 eq10
  have eq108 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose eq80 eq7
  have eq176 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1) ◇ X0)) = X1 := superpose eq7 eq108
  have eq186 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq108 eq7
  have eq189 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq108 eq11
  have eq441 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X0)))) := superpose eq186 eq189
  have eq448 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq106 eq441
  have eq583 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1) := superpose eq7 eq448
  have eq642 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq583 eq176
  have eq651 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq448 eq642
  have eq656 (X1 X3 : G) : (X1 ◇ ((X1 ◇ X3) ◇ (X3 ◇ X1))) = X3 := superpose eq651 eq106
  have eq774 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq651 eq656
  have eq776 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X2 := superpose eq774 eq13
  have eq1023 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq774 eq776
  have eq1024 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq774 eq1023
  have eq1025 (X0 X3 : G) : X0 = X3 := superpose eq1024 eq1024
  have eq1030 (X0 : G) : sK0 ≠ X0 := superpose eq1025 eq8
  subsumption eq1030 eq1025


@[equational_result]
theorem Equation9443_implies_Equation2 (G : Type*) [Magma G] (h : Equation9443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq109 eq30


@[equational_result]
theorem Equation9446_implies_Equation2 (G : Type*) [Magma G] (h : Equation9446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq10
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq14
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq7 eq32
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq138 eq70


@[equational_result]
theorem Equation9449_implies_Equation2 (G : Type*) [Magma G] (h : Equation9449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq7 eq10
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X3))) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq10 eq10
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq10
  have eq31 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq9 eq9
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq9 eq9
  have eq51 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq32
  have eq52 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ (X2 ◇ X0)) := superpose eq51 eq31
  have eq56 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ X1)) := superpose eq52 eq11
  have eq68 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X1)) := superpose eq56 eq12
  have eq71 (X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq68 eq10
  have eq97 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq71 eq13
  have eq100 (X0 X2 : G) : X0 = X2 := superpose eq71 eq97
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq100 eq8
  subsumption eq133 eq100


@[equational_result]
theorem Equation9451_implies_Equation2 (G : Type*) [Magma G] (h : Equation9451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X4 ◇ X0)))) := superpose eq9 eq9
  have eq23 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq7 eq9
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := superpose eq7 eq9
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) = X1 := superpose eq26 eq25
  have eq123 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq35
  have eq181 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq18 eq26
  have eq222 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq123 eq26
  have eq351 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq26 eq222
  have eq387 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq26 eq351
  have eq437 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq26 eq387
  have eq471 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq387 eq437
  have eq474 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq471 eq23
  have eq512 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq471 eq474
  have eq513 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq512 eq181
  have eq516 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq471 eq513
  have eq517 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq512 eq516
  have eq518 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq517 eq7
  have eq519 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) = ((X1 ◇ X0) ◇ X1) := superpose eq517 eq9
  have eq614 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq517 eq519
  have eq615 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq517 eq614
  have eq616 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq615 eq518
  have eq657 (X0 X2 : G) : X0 = X2 := superpose eq616 eq616
  have eq659 (X0 : G) : sK0 ≠ X0 := superpose eq657 eq8
  subsumption eq659 eq657


@[equational_result]
theorem Equation9452_implies_Equation2 (G : Type*) [Magma G] (h : Equation9452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq10 eq10
  have eq15 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq10 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X3 ◇ X3))) = (X1 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ (X4 ◇ X4)))) := superpose eq7 eq9
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = ((X0 ◇ X1) ◇ X0) := superpose eq10 eq9
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ X0)) := superpose eq10 eq9
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq9
  have eq57 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = ((X1 ◇ X0) ◇ X1) := superpose eq23 eq9
  have eq60 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ (X3 ◇ X3))) = (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X4 ◇ X4)))) := superpose eq57 eq17
  have eq72 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq30 eq57
  have eq74 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq72 eq15
  have eq78 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ (X3 ◇ X3))) = (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X4 ◇ X4)))) := superpose eq72 eq60
  have eq85 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ (X3 ◇ X3))) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq30 eq78
  have eq86 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X3 ◇ X3))) := superpose eq74 eq85
  have eq118 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := superpose eq14 eq37
  have eq119 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq118 eq86
  have eq125 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq119 eq10
  have eq133 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq119 eq125
  have eq134 (X0 X2 : G) : X0 = X2 := superpose eq133 eq133
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq134 eq8
  subsumption eq136 eq134


@[equational_result]
theorem Equation9453_implies_Equation2 (G : Type*) [Magma G] (h : Equation9453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq135 eq30


@[equational_result]
theorem Equation9455_implies_Equation2 (G : Type*) [Magma G] (h : Equation9455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X3 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq30 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq9
  have eq39 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ (((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X3 ◇ ((((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq11 eq30
  have eq43 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq30 eq30
  have eq45 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq30 eq7
  have eq90 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq45
  have eq91 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq11 eq45
  have eq92 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X3 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))))) := superpose eq10 eq45
  have eq94 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0))) = (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq9 eq45
  have eq110 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq90 eq7
  have eq111 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq90 eq9
  have eq112 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X3 ◇ X0))) = X1 := superpose eq90 eq10
  have eq125 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X3 ◇ ((((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ X0)) := superpose eq90 eq39
  have eq150 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq90 eq91
  have eq151 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq90 eq150
  have eq161 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq151 eq125
  have eq163 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq90 eq161
  have eq164 (X0 X1 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq90 eq92
  have eq165 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ X1)) := superpose eq110 eq164
  have eq166 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq165 eq112
  have eq177 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq166 eq163
  have eq192 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq90 eq94
  have eq193 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq177 eq192
  have eq194 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq193 eq111
  have eq205 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq110 eq194
  have eq206 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := superpose eq205 eq90
  have eq243 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq206 eq30
  have eq246 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq243 eq43
  have eq248 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq243 eq45
  have eq263 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq243 eq246
  have eq265 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq248 eq263
  have eq266 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq248 eq265
  have eq272 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq266 eq205
  have eq337 (X0 X1 : G) : X0 = X1 := superpose eq272 eq266
  have eq347 (X0 : G) : sK0 ≠ X0 := superpose eq337 eq8
  subsumption eq347 eq337


@[equational_result]
theorem Equation9457_implies_Equation2 (G : Type*) [Magma G] (h : Equation9457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9459_implies_Equation2 (G : Type*) [Magma G] (h : Equation9459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq9
  have eq40 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) := superpose eq9 eq10
  have eq51 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X0 := superpose eq25 eq40
  have eq52 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq51 eq10
  have eq73 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq51 eq52
  have eq175 (X0 X2 : G) : X0 = X2 := superpose eq73 eq73
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq175 eq8
  subsumption eq177 eq175


@[equational_result]
theorem Equation9460_implies_Equation2 (G : Type*) [Magma G] (h : Equation9460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation9461_implies_Equation2 (G : Type*) [Magma G] (h : Equation9461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9463_implies_Equation2 (G : Type*) [Magma G] (h : Equation9463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) = (X1 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) ◇ ((((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3) ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ (X3 ◇ X0)) ◇ (X5 ◇ (X5 ◇ (X0 ◇ X1))))) = ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X4 ◇ (X4 ◇ (X0 ◇ X1)))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X4 ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))))))) := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X4) ◇ (X5 ◇ (X5 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X0)))))) = ((X1 ◇ (X3 ◇ (X3 ◇ X0))) ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0)))))) := superpose eq9 eq9
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := superpose eq7 eq9
  have eq39 (X0 X1 X3 X4 X5 : G) : (((X1 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X4) ◇ (X5 ◇ (X5 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X0)))))) = ((X1 ◇ (X3 ◇ (X3 ◇ X0))) ◇ (X4 ◇ X1)) := superpose eq7 eq21
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ (X5 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0)))))) = (((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) ◇ (((((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) ◇ (X4 ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0)))))) ◇ (X0 ◇ X1))) := superpose eq9 eq10
  have eq63 (X0 X1 X2 X3 X5 : G) : (X3 ◇ (X5 ◇ (X5 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0)))))) = (((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq39 eq51
  have eq64 (X0 X1 X2 X3 X5 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X5 ◇ (X5 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0)))))) := superpose eq10 eq63
  have eq65 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq64 eq14
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X0)))) = X3 := superpose eq65 eq10
  have eq76 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) ◇ (X4 ◇ (X4 ◇ (X0 ◇ X1)))) := superpose eq9 eq28
  have eq79 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq9 eq28
  have eq101 (X0 X1 X3 X5 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ (X3 ◇ X0)) ◇ (X5 ◇ (X5 ◇ (X0 ◇ X1))))) = ((X0 ◇ X1) ◇ X0) := superpose eq79 eq13
  have eq112 (X0 X1 X2 X3 X5 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) = X5 := superpose eq68 eq68
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) = ((X0 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1))))) := superpose eq9 eq68
  have eq149 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X0))) = ((X0 ◇ X1) ◇ X0) := superpose eq101 eq127
  have eq158 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) = ((X1 ◇ X0) ◇ X1) := superpose eq149 eq9
  have eq190 (X0 X1 X3 X4 : G) : (X3 ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X4 ◇ (X4 ◇ (X0 ◇ X1)))) := superpose eq158 eq76
  have eq197 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X0 := superpose eq28 eq190
  have eq202 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq197 eq28
  have eq244 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq197 eq202
  have eq245 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) = X5 := superpose eq244 eq112
  have eq251 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X5 := superpose eq244 eq245
  have eq252 (X0 X1 X2 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = X5 := superpose eq244 eq251
  have eq253 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq244 eq252
  have eq276 (X0 X1 : G) : X0 = X1 := superpose eq244 eq253
  have eq281 (X0 : G) : sK0 ≠ X0 := superpose eq276 eq8
  subsumption eq281 eq276


@[equational_result]
theorem Equation9464_implies_Equation2 (G : Type*) [Magma G] (h : Equation9464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3)))) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X2 ◇ (X2 ◇ X2)))))) = X4 := superpose eq9 eq7
  have eq37 (X0 X3 X4 : G) : (X3 ◇ ((X3 ◇ X4) ◇ X0)) = X4 := superpose eq7 eq29
  have eq43 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq37
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq7 eq43
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq126 eq54


@[equational_result]
theorem Equation9465_implies_Equation2 (G : Type*) [Magma G] (h : Equation9465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation9467_implies_Equation2 (G : Type*) [Magma G] (h : Equation9467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0)) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X2 ◇ X3) := superpose eq11 eq7
  have eq71 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq20
  have eq179 (X0 X4 : G) : X0 = X4 := superpose eq7 eq71
  have eq296 (X0 : G) : sK0 ≠ X0 := superpose eq179 eq8
  subsumption eq296 eq179


@[equational_result]
theorem Equation9468_implies_Equation2 (G : Type*) [Magma G] (h : Equation9468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9469_implies_Equation2 (G : Type*) [Magma G] (h : Equation9469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation9470_implies_Equation2 (G : Type*) [Magma G] (h : Equation9470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9473_implies_Equation2 (G : Type*) [Magma G] (h : Equation9473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq9
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq9
  have eq19 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ X0) := superpose eq7 eq9
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq18 eq15
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq18 eq19
  have eq30 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq18 eq29
  have eq31 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq30 eq23
  have eq34 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq42 eq34


@[equational_result]
theorem Equation9476_implies_Equation2 (G : Type*) [Magma G] (h : Equation9476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ X0) := superpose eq7 eq9
  have eq21 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq9
  have eq31 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq21 eq7
  have eq33 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq21 eq31
  have eq34 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq33 eq7
  have eq39 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq33 eq15
  have eq42 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq33 eq39
  have eq43 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq42 eq34
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq43 eq43
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq50 eq48


@[equational_result]
theorem Equation9478_implies_Equation2 (G : Type*) [Magma G] (h : Equation9478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1)))) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq10 eq9
  have eq32 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := superpose eq26 eq7
  have eq47 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq26 eq32
  have eq48 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq26 eq47
  have eq49 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq26 eq48
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq49 eq49
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq57 eq55


@[equational_result]
theorem Equation9479_implies_Equation2 (G : Type*) [Magma G] (h : Equation9479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq7
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq15 eq9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := superpose eq20 eq7
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq20 eq10
  have eq26 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq20 eq21
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq20 eq22
  have eq28 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq20 eq27
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq28 eq26
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq29 eq29
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation9480_implies_Equation2 (G : Type*) [Magma G] (h : Equation9480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation9483_implies_Equation2 (G : Type*) [Magma G] (h : Equation9483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq42 eq16


@[equational_result]
theorem Equation9485_implies_Equation2 (G : Type*) [Magma G] (h : Equation9485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation9486_implies_Equation2 (G : Type*) [Magma G] (h : Equation9486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9488_implies_Equation2 (G : Type*) [Magma G] (h : Equation9488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9489_implies_Equation2 (G : Type*) [Magma G] (h : Equation9489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9490_implies_Equation2 (G : Type*) [Magma G] (h : Equation9490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9492_implies_Equation2 (G : Type*) [Magma G] (h : Equation9492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq7 eq10
  have eq27 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq10 eq9
  have eq39 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq27 eq10
  have eq40 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq27 eq13
  have eq70 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ X0) := superpose eq7 eq27
  have eq71 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq27 eq27
  have eq78 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq71 eq39
  have eq93 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq78 eq78
  have eq99 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1))))) = X2 := superpose eq78 eq7
  have eq108 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X2 ◇ X2)) := superpose eq93 eq40
  have eq123 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)))) = X2 := superpose eq108 eq99
  have eq124 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ X1)))) = X2 := superpose eq71 eq123
  have eq125 (X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = X2 := superpose eq70 eq124
  have eq126 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq125 eq108
  have eq128 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := superpose eq126 eq7
  have eq162 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq126 eq128
  have eq179 (X0 X2 : G) : X0 = X2 := superpose eq162 eq162
  have eq181 (X0 : G) : sK0 ≠ X0 := superpose eq179 eq8
  subsumption eq181 eq179


@[equational_result]
theorem Equation9494_implies_Equation2 (G : Type*) [Magma G] (h : Equation9494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation9496_implies_Equation2 (G : Type*) [Magma G] (h : Equation9496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation9497_implies_Equation2 (G : Type*) [Magma G] (h : Equation9497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9498_implies_Equation2 (G : Type*) [Magma G] (h : Equation9498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9500_implies_Equation2 (G : Type*) [Magma G] (h : Equation9500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9501_implies_Equation2 (G : Type*) [Magma G] (h : Equation9501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation9502_implies_Equation2 (G : Type*) [Magma G] (h : Equation9502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9504_implies_Equation2 (G : Type*) [Magma G] (h : Equation9504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9505_implies_Equation2 (G : Type*) [Magma G] (h : Equation9505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9506_implies_Equation2 (G : Type*) [Magma G] (h : Equation9506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9507_implies_Equation2 (G : Type*) [Magma G] (h : Equation9507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9509_implies_Equation2 (G : Type*) [Magma G] (h : Equation9509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq15 eq14
  have eq24 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X3 := superpose eq19 eq9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq24 eq15
  have eq39 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq31 eq24
  have eq46 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq31 eq39
  have eq49 (X0 X2 : G) : X0 = X2 := superpose eq46 eq46
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq51 eq49


@[equational_result]
theorem Equation9511_implies_Equation2 (G : Type*) [Magma G] (h : Equation9511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ (X4 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq7
  have eq23 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq21 eq12
  have eq26 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq21 eq23
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq32 eq27


@[equational_result]
theorem Equation9513_implies_Equation2 (G : Type*) [Magma G] (h : Equation9513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq62 eq24


@[equational_result]
theorem Equation9514_implies_Equation2 (G : Type*) [Magma G] (h : Equation9514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq107 eq31


@[equational_result]
theorem Equation9515_implies_Equation2 (G : Type*) [Magma G] (h : Equation9515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq12 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9517_implies_Equation2 (G : Type*) [Magma G] (h : Equation9517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1)))) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq7 eq9
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq18
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X1)))))) = X3 := superpose eq23 eq9
  have eq34 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq23 eq24
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq37 eq35


@[equational_result]
theorem Equation9518_implies_Equation2 (G : Type*) [Magma G] (h : Equation9518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) := superpose eq10 eq10
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))) = X2 := superpose eq10 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X3 ◇ (X0 ◇ ((((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))))))) := superpose eq10 eq9
  have eq29 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0))))) = X3 := superpose eq12 eq9
  have eq35 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq11
  have eq46 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))))) = (X1 ◇ (X3 ◇ (X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))))))) := superpose eq35 eq19
  have eq53 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))))) = X0 := superpose eq9 eq46
  have eq56 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X3 := superpose eq53 eq9
  have eq63 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0))) = X3 := superpose eq56 eq29
  have eq78 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq56 eq63
  have eq79 (X0 X3 : G) : X0 = X3 := superpose eq78 eq78
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq87 eq79


@[equational_result]
theorem Equation9519_implies_Equation2 (G : Type*) [Magma G] (h : Equation9519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq15 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = X3 := superpose eq12 eq10
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq29 eq20


@[equational_result]
theorem Equation9521_implies_Equation2 (G : Type*) [Magma G] (h : Equation9521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ (X5 ◇ X1)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq9 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq11 eq17
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq126 eq41


@[equational_result]
theorem Equation9522_implies_Equation2 (G : Type*) [Magma G] (h : Equation9522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0)) = X4 := superpose eq7 eq7
  have eq50 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq69 eq50


@[equational_result]
theorem Equation9523_implies_Equation2 (G : Type*) [Magma G] (h : Equation9523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ (X5 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X4 := superpose eq7 eq10
  have eq21 (X1 X4 X5 : G) : (X1 ◇ (X5 ◇ X5)) = X4 := superpose eq12 eq9
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq36 eq28


@[equational_result]
theorem Equation9524_implies_Equation2 (G : Type*) [Magma G] (h : Equation9524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation9526_implies_Equation2 (G : Type*) [Magma G] (h : Equation9526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq9
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq13 eq9
  have eq36 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq14
  have eq54 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq36 eq7
  have eq63 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq54 eq35
  have eq76 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq63 eq54
  have eq112 (X0 X2 : G) : X0 = X2 := superpose eq76 eq76
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq112 eq8
  subsumption eq114 eq112


@[equational_result]
theorem Equation9528_implies_Equation2 (G : Type*) [Magma G] (h : Equation9528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X4 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq7 eq9
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq16 eq7
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq34 eq25


@[equational_result]
theorem Equation9530_implies_Equation2 (G : Type*) [Magma G] (h : Equation9530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9531_implies_Equation2 (G : Type*) [Magma G] (h : Equation9531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation9532_implies_Equation2 (G : Type*) [Magma G] (h : Equation9532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9534_implies_Equation2 (G : Type*) [Magma G] (h : Equation9534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9535_implies_Equation2 (G : Type*) [Magma G] (h : Equation9535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9536_implies_Equation2 (G : Type*) [Magma G] (h : Equation9536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9538_implies_Equation2 (G : Type*) [Magma G] (h : Equation9538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9539_implies_Equation2 (G : Type*) [Magma G] (h : Equation9539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9540_implies_Equation2 (G : Type*) [Magma G] (h : Equation9540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9541_implies_Equation2 (G : Type*) [Magma G] (h : Equation9541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9545_implies_Equation2 (G : Type*) [Magma G] (h : Equation9545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq67 eq19


@[equational_result]
theorem Equation9547_implies_Equation2 (G : Type*) [Magma G] (h : Equation9547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9548_implies_Equation2 (G : Type*) [Magma G] (h : Equation9548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation9549_implies_Equation2 (G : Type*) [Magma G] (h : Equation9549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9551_implies_Equation2 (G : Type*) [Magma G] (h : Equation9551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9552_implies_Equation2 (G : Type*) [Magma G] (h : Equation9552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9553_implies_Equation2 (G : Type*) [Magma G] (h : Equation9553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9555_implies_Equation2 (G : Type*) [Magma G] (h : Equation9555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9556_implies_Equation2 (G : Type*) [Magma G] (h : Equation9556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9557_implies_Equation2 (G : Type*) [Magma G] (h : Equation9557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9558_implies_Equation2 (G : Type*) [Magma G] (h : Equation9558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9560_implies_Equation2 (G : Type*) [Magma G] (h : Equation9560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ (X5 ◇ X1)))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = X3 := superpose eq7 eq9
  have eq61 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq146 eq61


@[equational_result]
theorem Equation9561_implies_Equation2 (G : Type*) [Magma G] (h : Equation9561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq64 eq13


@[equational_result]
theorem Equation9562_implies_Equation2 (G : Type*) [Magma G] (h : Equation9562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation9563_implies_Equation2 (G : Type*) [Magma G] (h : Equation9563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9565_implies_Equation2 (G : Type*) [Magma G] (h : Equation9565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9566_implies_Equation2 (G : Type*) [Magma G] (h : Equation9566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9567_implies_Equation2 (G : Type*) [Magma G] (h : Equation9567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9568_implies_Equation2 (G : Type*) [Magma G] (h : Equation9568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9570_implies_Equation2 (G : Type*) [Magma G] (h : Equation9570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9571_implies_Equation2 (G : Type*) [Magma G] (h : Equation9571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9572_implies_Equation2 (G : Type*) [Magma G] (h : Equation9572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9573_implies_Equation2 (G : Type*) [Magma G] (h : Equation9573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9575_implies_Equation2 (G : Type*) [Magma G] (h : Equation9575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9576_implies_Equation2 (G : Type*) [Magma G] (h : Equation9576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9577_implies_Equation2 (G : Type*) [Magma G] (h : Equation9577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9578_implies_Equation2 (G : Type*) [Magma G] (h : Equation9578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9580_implies_Equation2 (G : Type*) [Magma G] (h : Equation9580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9581_implies_Equation2 (G : Type*) [Magma G] (h : Equation9581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9582_implies_Equation2 (G : Type*) [Magma G] (h : Equation9582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9583_implies_Equation2 (G : Type*) [Magma G] (h : Equation9583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9584_implies_Equation2 (G : Type*) [Magma G] (h : Equation9584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9586_implies_Equation2 (G : Type*) [Magma G] (h : Equation9586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ (X3 ◇ X0)))) ◇ X0) := superpose eq7 eq10
  have eq23 (X0 X1 X3 X4 : G) : ((X4 ◇ X0) ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (((X4 ◇ X0) ◇ (X0 ◇ X3)) ◇ (((X4 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1)))) := superpose eq10 eq7
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq11 eq11
  have eq29 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq11 eq11
  have eq30 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X0 ◇ X1)) := superpose eq11 eq10
  have eq41 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = (((X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)))) ◇ X0) := superpose eq7 eq30
  have eq71 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = (((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X4 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1))) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) ◇ X1))) := superpose eq9 eq10
  have eq86 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) := superpose eq11 eq29
  have eq87 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = ((X2 ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2))) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) := superpose eq29 eq29
  have eq115 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = (X4 ◇ (X2 ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X4)))) := superpose eq7 eq23
  have eq163 (X0 X2 X4 : G) : (X4 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X4)))) = X0 := superpose eq7 eq115
  have eq261 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)))) := superpose eq11 eq163
  have eq266 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X1 := superpose eq163 eq163
  have eq269 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq163 eq163
  have eq271 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq163 eq30
  have eq311 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq266 eq261
  have eq314 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0))))) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X0) := superpose eq266 eq21
  have eq325 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq311 eq26
  have eq371 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq325 eq163
  have eq406 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = (((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) ◇ X1))) := superpose eq371 eq71
  have eq407 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = (((X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)))) ◇ X0) := superpose eq371 eq41
  have eq465 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0))))) ◇ ((X3 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X0) := superpose eq371 eq314
  have eq498 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = (((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X1 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) ◇ X1))) := superpose eq371 eq406
  have eq499 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = (((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X1 ◇ X1)) := superpose eq269 eq498
  have eq500 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) := superpose eq371 eq499
  have eq503 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = (((X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq500 eq407
  have eq504 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq371 eq503
  have eq505 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq371 eq504
  have eq540 (X0 X2 X3 : G) : (X3 ◇ X0) = (((X2 ◇ (X3 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X0) := superpose eq371 eq465
  have eq541 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = (X0 ◇ X0) := superpose eq540 eq505
  have eq566 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) = X3 := superpose eq9 eq269
  have eq613 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq566 eq541
  have eq645 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq613 eq271
  have eq656 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq613 eq645
  have eq657 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = ((X2 ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2))) ◇ X2) := superpose eq656 eq87
  have eq658 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X2 := superpose eq269 eq657
  have eq660 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) := superpose eq658 eq86
  have eq661 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq269 eq660
  have eq662 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))) ◇ X1) := superpose eq661 eq29
  have eq676 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq269 eq662
  have eq678 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq676 eq11
  have eq702 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq269 eq678
  have eq703 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq702 eq7
  have eq785 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq702 eq703
  have eq786 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq702 eq785
  have eq787 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq702 eq786
  have eq1333 (X0 X2 : G) : X0 = X2 := superpose eq787 eq787
  have eq1335 (X0 : G) : sK0 ≠ X0 := superpose eq1333 eq8
  subsumption eq1335 eq1333


@[equational_result]
theorem Equation9587_implies_Equation2 (G : Type*) [Magma G] (h : Equation9587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ (((((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1)) ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := superpose eq7 eq11
  have eq25 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq7 eq16
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := superpose eq25 eq7
  have eq38 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq25 eq29
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq25 eq38
  have eq40 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq25 eq39
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq40 eq40
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq43 eq41


@[equational_result]
theorem Equation9588_implies_Equation2 (G : Type*) [Magma G] (h : Equation9588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X3)))) = (X4 ◇ X0) := superpose eq7 eq11
  have eq42 (X0 X4 : G) : (X4 ◇ X0) = X0 := superpose eq7 eq31
  have eq43 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := superpose eq42 eq7
  have eq52 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq42 eq43
  have eq53 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq42 eq52
  have eq54 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq42 eq53
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq54 eq54
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq57 eq55


@[equational_result]
theorem Equation9590_implies_Equation2 (G : Type*) [Magma G] (h : Equation9590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (((X3 ◇ X0) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)))) := superpose eq10 eq7
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq10 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = (X3 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)))) := superpose eq10 eq9
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X3))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X3))) ◇ X0))) := superpose eq10 eq9
  have eq28 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq9
  have eq32 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq28
  have eq35 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq32
  have eq90 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X2 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq35 eq35
  have eq97 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq35 eq35
  have eq101 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X1 := superpose eq35 eq10
  have eq118 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))))) = X3 := superpose eq35 eq7
  have eq123 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq35 eq32
  have eq143 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X1 := superpose eq101 eq97
  have eq149 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) := superpose eq101 eq123
  have eq180 (X0 X1 X2 X3 : G) : ((((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ ((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) = X2 := superpose eq16 eq17
  have eq269 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))))) = ((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))))) := superpose eq16 eq90
  have eq396 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ ((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) = X2 := superpose eq269 eq180
  have eq685 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X3 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) = ((X1 ◇ X1) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (((X3 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))))) := superpose eq35 eq19
  have eq763 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq149 eq26
  have eq772 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0))) := superpose eq149 eq17
  have eq798 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq763
  have eq945 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq143 eq798
  have eq1041 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose eq149 eq945
  have eq1042 (X0 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq1041 eq772
  have eq1043 (X0 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq1042
  have eq1053 (X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) = X3 := superpose eq1043 eq118
  have eq1060 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ X1) = X2 := superpose eq1043 eq396
  have eq1063 (X1 X2 X3 X4 : G) : (X2 ◇ (((X3 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) = ((X1 ◇ X1) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1)) := superpose eq1043 eq685
  have eq1136 (X2 X3 X4 : G) : (X2 ◇ X2) = (X2 ◇ (((X3 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) := superpose eq1053 eq1063
  have eq1166 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) = X2 := superpose eq1136 eq1060
  have eq1173 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq1043 eq1166
  have eq1413 (X0 X1 : G) : X0 = X1 := superpose eq10 eq1173
  have eq1612 (X0 : G) : sK0 ≠ X0 := superpose eq1413 eq8
  subsumption eq1612 eq1413


@[equational_result]
theorem Equation9592_implies_Equation2 (G : Type*) [Magma G] (h : Equation9592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X3 := superpose eq12 eq7
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq44 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq26 eq16
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq108 eq46


@[equational_result]
theorem Equation9595_implies_Equation2 (G : Type*) [Magma G] (h : Equation9595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq11 eq7
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq18
  have eq22 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq21
  have eq23 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq22 eq7
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq22 eq11
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq22 eq26
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq34 eq23
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq34 eq36
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq34 eq41
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq42 eq42
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation9596_implies_Equation2 (G : Type*) [Magma G] (h : Equation9596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X0) := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X1 := superpose eq12 eq7
  have eq39 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq12 eq10
  have eq52 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq39 eq23
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq10 eq52
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq100 eq55


@[equational_result]
theorem Equation9598_implies_Equation2 (G : Type*) [Magma G] (h : Equation9598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X3 : G) : (X3 ◇ X0) = (X1 ◇ X0) := superpose eq11 eq7
  have eq42 (X0 X1 X3 X4 : G) : (X4 ◇ ((X3 ◇ X0) ◇ X1)) = X0 := superpose eq11 eq21
  have eq151 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq42
  have eq237 (X0 X4 : G) : X0 = X4 := superpose eq7 eq151
  have eq433 (X0 : G) : sK0 ≠ X0 := superpose eq237 eq8
  subsumption eq433 eq237


@[equational_result]
theorem Equation9599_implies_Equation2 (G : Type*) [Magma G] (h : Equation9599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0)) = X4 := superpose eq7 eq7
  have eq41 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq11
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq148 eq54


@[equational_result]
theorem Equation9600_implies_Equation2 (G : Type*) [Magma G] (h : Equation9600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) = X3 := superpose eq7 eq7
  have eq34 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq11
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq7 eq34
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq123 eq43


@[equational_result]
theorem Equation9601_implies_Equation2 (G : Type*) [Magma G] (h : Equation9601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq34 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq46 (X0 X5 : G) : X0 = X5 := superpose eq7 eq34
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq106 eq46


@[equational_result]
theorem Equation9605_implies_Equation2 (G : Type*) [Magma G] (h : Equation9605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X1)) = (X4 ◇ (X0 ◇ X1)) := superpose eq11 eq11
  have eq38 (X0 X1 X4 : G) : (X0 ◇ X1) = (X4 ◇ (X0 ◇ X1)) := superpose eq14 eq28
  have eq45 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq38 eq10
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq45 eq45
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq68 eq60


@[equational_result]
theorem Equation9607_implies_Equation2 (G : Type*) [Magma G] (h : Equation9607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X2 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X4 ◇ (X4 ◇ X4)))) = (X0 ◇ (X3 ◇ (X3 ◇ X3))) := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := superpose eq7 eq9
  have eq27 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X3))) = (X4 ◇ (X1 ◇ X1)) := superpose eq17 eq10
  have eq114 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ X5)) = X0 := superpose eq17 eq27
  have eq178 (X0 X3 : G) : X0 = X3 := superpose eq114 eq114
  have eq272 (X0 : G) : sK0 ≠ X0 := superpose eq178 eq8
  subsumption eq272 eq178


@[equational_result]
theorem Equation9609_implies_Equation2 (G : Type*) [Magma G] (h : Equation9609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ (X2 ◇ (X2 ◇ X4))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X5)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := superpose eq12 eq7
  have eq18 (X0 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ (X2 ◇ (X2 ◇ X4))) = X0 := superpose eq17 eq9
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq18 eq7
  have eq21 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X1 ◇ X0))) = X3 := superpose eq20 eq10
  have eq27 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq20 eq21
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq20 eq27
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq34 eq29


@[equational_result]
theorem Equation9611_implies_Equation2 (G : Type*) [Magma G] (h : Equation9611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ ((X2 ◇ X3) ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X1)) ◇ (X4 ◇ (X3 ◇ X4))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq9
  have eq35 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) = X1 := superpose eq26 eq25
  have eq97 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq35
  have eq124 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq97 eq35
  have eq142 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq97 eq10
  have eq146 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq26 eq142
  have eq147 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq124 eq146
  have eq148 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := superpose eq147 eq7
  have eq246 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq147 eq148
  have eq247 (X0 X3 : G) : X0 = X3 := superpose eq246 eq246
  have eq249 (X0 : G) : sK0 ≠ X0 := superpose eq247 eq8
  subsumption eq249 eq247


@[equational_result]
theorem Equation9613_implies_Equation2 (G : Type*) [Magma G] (h : Equation9613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) = (X1 ◇ (X0 ◇ X3)) := superpose eq7 eq11
  have eq35 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X3 := superpose eq14 eq24
  have eq40 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq35 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq11 eq40
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq72 eq41


@[equational_result]
theorem Equation9615_implies_Equation2 (G : Type*) [Magma G] (h : Equation9615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq11 eq11
  have eq21 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X0 := superpose eq13 eq7
  have eq34 (X0 X1 : G) : X0 = X1 := superpose eq21 eq13
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq75 eq34


@[equational_result]
theorem Equation9616_implies_Equation2 (G : Type*) [Magma G] (h : Equation9616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation9617_implies_Equation2 (G : Type*) [Magma G] (h : Equation9617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation9618_implies_Equation2 (G : Type*) [Magma G] (h : Equation9618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq43 eq16


@[equational_result]
theorem Equation9621_implies_Equation2 (G : Type*) [Magma G] (h : Equation9621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) ◇ (((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0))) = X3 := superpose eq12 eq10
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) = X3 := superpose eq12 eq14
  have eq20 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq19
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq26 eq21


@[equational_result]
theorem Equation9622_implies_Equation2 (G : Type*) [Magma G] (h : Equation9622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9624_implies_Equation2 (G : Type*) [Magma G] (h : Equation9624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq43 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) = ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) := superpose eq9 eq9
  have eq69 (X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq43
  have eq70 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq69 eq7
  have eq112 (X0 X2 : G) : X0 = X2 := superpose eq10 eq70
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq112 eq8
  subsumption eq125 eq112


@[equational_result]
theorem Equation9625_implies_Equation2 (G : Type*) [Magma G] (h : Equation9625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X2 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) ◇ (((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X1)) ◇ (X3 ◇ (X4 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2))))) := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := superpose eq7 eq9
  have eq36 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2))))) = X1 := superpose eq26 eq25
  have eq77 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))))) := superpose eq26 eq7
  have eq91 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq36
  have eq92 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X0))))) = X1 := superpose eq9 eq36
  have eq108 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq92
  have eq109 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq9 eq91
  have eq123 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X2 ◇ X2) := superpose eq7 eq109
  have eq126 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ X0))) = X3 := superpose eq123 eq10
  have eq174 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))))) := superpose eq123 eq77
  have eq271 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X0))))) := superpose eq123 eq174
  have eq272 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq108 eq271
  have eq274 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ ((X2 ◇ X2) ◇ X0))) = X3 := superpose eq272 eq126
  have eq379 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) = X2 := superpose eq91 eq274
  have eq385 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq91 eq274
  have eq390 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X0)) = X3 := superpose eq385 eq274
  have eq402 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq385 eq390
  have eq403 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq402 eq379
  have eq407 (X0 X1 : G) : X0 = X1 := superpose eq91 eq403
  have eq422 (X0 : G) : sK0 ≠ X0 := superpose eq407 eq8
  subsumption eq422 eq407


@[equational_result]
theorem Equation9626_implies_Equation2 (G : Type*) [Magma G] (h : Equation9626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9629_implies_Equation2 (G : Type*) [Magma G] (h : Equation9629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X3 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq50 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((((X1 ◇ (X3 ◇ (X3 ◇ X3))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X4) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))))) = X4 := superpose eq9 eq11
  have eq64 (X1 X2 X4 : G) : (X2 ◇ X1) = X4 := superpose eq7 eq50
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq7 eq64
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq161 eq65


@[equational_result]
theorem Equation9630_implies_Equation2 (G : Type*) [Magma G] (h : Equation9630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X0))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq138 eq36


@[equational_result]
theorem Equation9632_implies_Equation2 (G : Type*) [Magma G] (h : Equation9632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X4) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq12 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq44 eq35


@[equational_result]
theorem Equation9633_implies_Equation2 (G : Type*) [Magma G] (h : Equation9633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation9634_implies_Equation2 (G : Type*) [Magma G] (h : Equation9634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9635_implies_Equation2 (G : Type*) [Magma G] (h : Equation9635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9637_implies_Equation2 (G : Type*) [Magma G] (h : Equation9637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq12 eq12
  have eq15 (X0 X1 X3 : G) : (X0 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := superpose eq7 eq12
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq12 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq15 eq12
  have eq38 (X1 X3 : G) : (X1 ◇ X3) = X3 := superpose eq25 eq20
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq38 eq14
  have eq47 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq52 eq47


@[equational_result]
theorem Equation9638_implies_Equation2 (G : Type*) [Magma G] (h : Equation9638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation9639_implies_Equation2 (G : Type*) [Magma G] (h : Equation9639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation9640_implies_Equation2 (G : Type*) [Magma G] (h : Equation9640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9642_implies_Equation2 (G : Type*) [Magma G] (h : Equation9642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq40 eq15


@[equational_result]
theorem Equation9643_implies_Equation2 (G : Type*) [Magma G] (h : Equation9643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ (X3 ◇ X1)) ◇ X4) ◇ X0)) = X4 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ X0) := superpose eq11 eq7
  have eq74 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq7 eq22
  have eq191 (X0 X4 : G) : X0 = X4 := superpose eq7 eq74
  have eq319 (X0 : G) : sK0 ≠ X0 := superpose eq191 eq8
  subsumption eq319 eq191


@[equational_result]
theorem Equation9644_implies_Equation2 (G : Type*) [Magma G] (h : Equation9644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation9645_implies_Equation2 (G : Type*) [Magma G] (h : Equation9645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9647_implies_Equation2 (G : Type*) [Magma G] (h : Equation9647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq45 eq17


@[equational_result]
theorem Equation9648_implies_Equation2 (G : Type*) [Magma G] (h : Equation9648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq46 eq13


@[equational_result]
theorem Equation9649_implies_Equation2 (G : Type*) [Magma G] (h : Equation9649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation9650_implies_Equation2 (G : Type*) [Magma G] (h : Equation9650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9652_implies_Equation2 (G : Type*) [Magma G] (h : Equation9652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X3 ◇ X4) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq37 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq12 eq11
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq37
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq165 eq48


@[equational_result]
theorem Equation9653_implies_Equation2 (G : Type*) [Magma G] (h : Equation9653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation9654_implies_Equation2 (G : Type*) [Magma G] (h : Equation9654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (((X4 ◇ X0) ◇ (X5 ◇ (X5 ◇ X5))) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq11
  have eq22 (X1 X3 X5 : G) : (X1 ◇ (X5 ◇ (X5 ◇ X5))) = X3 := superpose eq14 eq10
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq11 eq22
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq48 eq30


@[equational_result]
theorem Equation9655_implies_Equation2 (G : Type*) [Magma G] (h : Equation9655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9657_implies_Equation2 (G : Type*) [Magma G] (h : Equation9657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq43 eq17


@[equational_result]
theorem Equation9658_implies_Equation2 (G : Type*) [Magma G] (h : Equation9658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation9659_implies_Equation2 (G : Type*) [Magma G] (h : Equation9659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation9660_implies_Equation2 (G : Type*) [Magma G] (h : Equation9660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9661_implies_Equation2 (G : Type*) [Magma G] (h : Equation9661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation9665_implies_Equation2 (G : Type*) [Magma G] (h : Equation9665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq25 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X0 := superpose eq10 eq11
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq25
  have eq50 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := superpose eq38 eq7
  have eq69 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq38 eq50
  have eq70 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq38 eq69
  have eq71 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq38 eq70
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq71 eq71
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq74 eq72


@[equational_result]
theorem Equation9669_implies_Equation2 (G : Type*) [Magma G] (h : Equation9669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (((X3 ◇ X2) ◇ (X0 ◇ (X2 ◇ X4))) ◇ ((X3 ◇ X2) ◇ (X0 ◇ (X2 ◇ X4)))) := superpose eq7 eq12
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq12 eq12
  have eq16 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq7 eq12
  have eq30 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = ((X0 ◇ (X2 ◇ X4)) ◇ (X0 ◇ (X2 ◇ X4))) := superpose eq15 eq13
  have eq33 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq16 eq30
  have eq35 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X0))) = X3 := superpose eq33 eq10
  have eq42 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq33 eq35
  have eq43 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq33 eq42
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq46 eq44


@[equational_result]
theorem Equation9671_implies_Equation2 (G : Type*) [Magma G] (h : Equation9671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = (X4 ◇ (X0 ◇ X4)) := superpose eq9 eq10
  have eq73 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))) = X2 := superpose eq20 eq7
  have eq85 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) = X1 := superpose eq20 eq7
  have eq113 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq85 eq73
  have eq116 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq113 eq7
  have eq144 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq113 eq116
  have eq145 (X0 X3 : G) : X0 = X3 := superpose eq144 eq144
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq145 eq8
  subsumption eq147 eq145


@[equational_result]
theorem Equation9673_implies_Equation2 (G : Type*) [Magma G] (h : Equation9673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X3 := superpose eq12 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq15 eq12
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X3 := superpose eq17 eq11
  have eq22 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = X3 := superpose eq17 eq18
  have eq23 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq17 eq22
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq29 eq24


@[equational_result]
theorem Equation9675_implies_Equation2 (G : Type*) [Magma G] (h : Equation9675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) ◇ ((X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2)))) ◇ (X5 ◇ X0))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq134 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq11 eq10
  have eq155 (X0 X4 : G) : X0 = X4 := superpose eq7 eq134
  have eq276 (X0 : G) : sK0 ≠ X0 := superpose eq155 eq8
  subsumption eq276 eq155


@[equational_result]
theorem Equation9676_implies_Equation2 (G : Type*) [Magma G] (h : Equation9676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = X0 := superpose eq7 eq12
  have eq36 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X0)) = X4 := superpose eq22 eq11
  have eq45 (X0 X2 : G) : X0 = X2 := superpose eq7 eq36
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq68 eq45


@[equational_result]
theorem Equation9677_implies_Equation2 (G : Type*) [Magma G] (h : Equation9677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X1 ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq67 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq163 eq67


@[equational_result]
theorem Equation9678_implies_Equation2 (G : Type*) [Magma G] (h : Equation9678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation9682_implies_Equation2 (G : Type*) [Magma G] (h : Equation9682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation9684_implies_Equation2 (G : Type*) [Magma G] (h : Equation9684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9685_implies_Equation2 (G : Type*) [Magma G] (h : Equation9685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9686_implies_Equation2 (G : Type*) [Magma G] (h : Equation9686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9688_implies_Equation2 (G : Type*) [Magma G] (h : Equation9688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation9689_implies_Equation2 (G : Type*) [Magma G] (h : Equation9689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9690_implies_Equation2 (G : Type*) [Magma G] (h : Equation9690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9692_implies_Equation2 (G : Type*) [Magma G] (h : Equation9692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9693_implies_Equation2 (G : Type*) [Magma G] (h : Equation9693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9694_implies_Equation2 (G : Type*) [Magma G] (h : Equation9694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9695_implies_Equation2 (G : Type*) [Magma G] (h : Equation9695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9699_implies_Equation2 (G : Type*) [Magma G] (h : Equation9699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X0))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq67 eq19


@[equational_result]
theorem Equation9701_implies_Equation2 (G : Type*) [Magma G] (h : Equation9701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9702_implies_Equation2 (G : Type*) [Magma G] (h : Equation9702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9703_implies_Equation2 (G : Type*) [Magma G] (h : Equation9703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9705_implies_Equation2 (G : Type*) [Magma G] (h : Equation9705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation9706_implies_Equation2 (G : Type*) [Magma G] (h : Equation9706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9707_implies_Equation2 (G : Type*) [Magma G] (h : Equation9707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9709_implies_Equation2 (G : Type*) [Magma G] (h : Equation9709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9710_implies_Equation2 (G : Type*) [Magma G] (h : Equation9710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9711_implies_Equation2 (G : Type*) [Magma G] (h : Equation9711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9712_implies_Equation2 (G : Type*) [Magma G] (h : Equation9712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9714_implies_Equation2 (G : Type*) [Magma G] (h : Equation9714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X4 ◇ (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))))))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X3)))) = ((X5 ◇ X0) ◇ ((X6 ◇ (X5 ◇ X0)) ◇ X3)) := superpose eq7 eq11
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq11 eq11
  have eq29 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X4 ◇ X1)) = (((X2 ◇ (X3 ◇ (X4 ◇ X1))) ◇ X4) ◇ ((X5 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X1))) ◇ X4)) ◇ (X6 ◇ (X0 ◇ X1)))) := superpose eq11 eq7
  have eq45 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X3))) ◇ (X5 ◇ (X7 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X3))))) ◇ ((X6 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X3)))))) ◇ X1))))) = X8 := superpose eq11 eq9
  have eq52 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X3))))) ◇ ((X6 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X3)))))) ◇ X0)) = X5 := superpose eq9 eq7
  have eq56 (X2 X3 X4 X5 X7 X8 : G) : (((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X3))) ◇ (X5 ◇ (X7 ◇ X5))) = X8 := superpose eq52 eq45
  have eq57 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq23
  have eq109 (X0 X3 X5 X6 : G) : ((X5 ◇ X0) ◇ ((X6 ◇ (X5 ◇ X0)) ◇ X3)) = X0 := superpose eq57 eq13
  have eq134 (X1 X3 X4 : G) : (X3 ◇ (X4 ◇ X1)) = X4 := superpose eq109 eq29
  have eq138 (X2 X3 X4 X5 X7 X8 : G) : (((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X3))) ◇ X7) = X8 := superpose eq134 eq56
  have eq161 (X4 X7 X8 : G) : (X4 ◇ X7) = X8 := superpose eq134 eq138
  have eq162 (X0 X3 : G) : X0 = X3 := superpose eq161 eq161
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq162 eq8
  subsumption eq170 eq162


@[equational_result]
theorem Equation9715_implies_Equation2 (G : Type*) [Magma G] (h : Equation9715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq64 eq13


@[equational_result]
theorem Equation9716_implies_Equation2 (G : Type*) [Magma G] (h : Equation9716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (((X3 ◇ X4) ◇ (X5 ◇ (X0 ◇ X5))) ◇ X0))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X4) = X0 := superpose eq7 eq12
  have eq29 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X4 := superpose eq13 eq10
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq29
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq59 eq40


@[equational_result]
theorem Equation9717_implies_Equation2 (G : Type*) [Magma G] (h : Equation9717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation9719_implies_Equation2 (G : Type*) [Magma G] (h : Equation9719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9720_implies_Equation2 (G : Type*) [Magma G] (h : Equation9720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9721_implies_Equation2 (G : Type*) [Magma G] (h : Equation9721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9722_implies_Equation2 (G : Type*) [Magma G] (h : Equation9722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9724_implies_Equation2 (G : Type*) [Magma G] (h : Equation9724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9725_implies_Equation2 (G : Type*) [Magma G] (h : Equation9725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9726_implies_Equation2 (G : Type*) [Magma G] (h : Equation9726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9727_implies_Equation2 (G : Type*) [Magma G] (h : Equation9727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9729_implies_Equation2 (G : Type*) [Magma G] (h : Equation9729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9730_implies_Equation2 (G : Type*) [Magma G] (h : Equation9730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9731_implies_Equation2 (G : Type*) [Magma G] (h : Equation9731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9732_implies_Equation2 (G : Type*) [Magma G] (h : Equation9732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9734_implies_Equation2 (G : Type*) [Magma G] (h : Equation9734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9735_implies_Equation2 (G : Type*) [Magma G] (h : Equation9735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9736_implies_Equation2 (G : Type*) [Magma G] (h : Equation9736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9737_implies_Equation2 (G : Type*) [Magma G] (h : Equation9737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9738_implies_Equation2 (G : Type*) [Magma G] (h : Equation9738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9741_implies_Equation2 (G : Type*) [Magma G] (h : Equation9741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq15 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq7 eq12
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq15 eq7
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq15 eq20
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq15 eq24
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation9742_implies_Equation2 (G : Type*) [Magma G] (h : Equation9742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ (X4 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq7 eq12
  have eq18 (X1 X4 X5 : G) : (X1 ◇ (X4 ◇ (X4 ◇ X5))) = X4 := superpose eq13 eq9
  have eq23 (X1 X4 X5 : G) : (X1 ◇ (X4 ◇ X5)) = X4 := superpose eq13 eq18
  have eq24 (X1 X4 X5 : G) : (X1 ◇ X5) = X4 := superpose eq13 eq23
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation9744_implies_Equation2 (G : Type*) [Magma G] (h : Equation9744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq10
  have eq51 (X0 X1 : G) : X0 = X1 := superpose eq9 eq28
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq125 eq51


@[equational_result]
theorem Equation9745_implies_Equation2 (G : Type*) [Magma G] (h : Equation9745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = (X1 ◇ X0) := superpose eq10 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (X3 ◇ X0))) = X3 := superpose eq10 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0)) ◇ ((((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0))) ◇ (X4 ◇ X3))) = X4 := superpose eq7 eq9
  have eq48 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X1 := superpose eq15 eq10
  have eq79 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq13 eq9
  have eq118 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X0 ◇ X0) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0))) := superpose eq48 eq13
  have eq120 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq48 eq10
  have eq123 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((((((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)) ◇ ((((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0))) ◇ (X4 ◇ X3))) = X4 := superpose eq48 eq9
  have eq141 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (((((X2 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) ◇ (((X2 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))))) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X3)))) := superpose eq9 eq14
  have eq148 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4))) = ((X0 ◇ X1) ◇ ((X3 ◇ X3) ◇ (X4 ◇ X4))) := superpose eq15 eq14
  have eq206 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X3)))) := superpose eq15 eq141
  have eq216 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X0))) ◇ (X4 ◇ X3))) = X4 := superpose eq148 eq18
  have eq217 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X0))) ◇ (X4 ◇ X3))) = X4 := superpose eq148 eq123
  have eq221 (X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) = X4 := superpose eq120 eq217
  have eq224 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq221 eq206
  have eq237 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X0))) = X3 := superpose eq224 eq17
  have eq257 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X1 := superpose eq237 eq118
  have eq259 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq257 eq79
  have eq263 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X0))) ◇ (X4 ◇ X3))) = X4 := superpose eq257 eq216
  have eq275 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq257 eq120
  have eq303 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq257 eq259
  have eq311 (X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) = X4 := superpose eq275 eq263
  have eq314 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq311 eq15
  have eq346 (X0 X1 : G) : X0 = X1 := superpose eq314 eq303
  have eq351 (X0 : G) : sK0 ≠ X0 := superpose eq346 eq8
  subsumption eq351 eq346


@[equational_result]
theorem Equation9746_implies_Equation2 (G : Type*) [Magma G] (h : Equation9746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq7
  have eq24 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq9 eq9
  have eq43 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq24 eq7
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq9 eq43
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq103 eq44


@[equational_result]
theorem Equation9749_implies_Equation2 (G : Type*) [Magma G] (h : Equation9749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X0 := superpose eq10 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq10 eq11
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9750_implies_Equation2 (G : Type*) [Magma G] (h : Equation9750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq131 eq48


@[equational_result]
theorem Equation9752_implies_Equation2 (G : Type*) [Magma G] (h : Equation9752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ (X2 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq154 eq56


@[equational_result]
theorem Equation9753_implies_Equation2 (G : Type*) [Magma G] (h : Equation9753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq128 eq45


@[equational_result]
theorem Equation9754_implies_Equation2 (G : Type*) [Magma G] (h : Equation9754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ (X5 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq32 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq53 (X1 X4 X5 : G) : (X1 ◇ X5) = X4 := superpose eq32 eq9
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq53 eq53
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq88 eq57


@[equational_result]
theorem Equation9755_implies_Equation2 (G : Type*) [Magma G] (h : Equation9755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation9759_implies_Equation2 (G : Type*) [Magma G] (h : Equation9759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((X4 ◇ X4) ◇ ((X0 ◇ X0) ◇ X1))) = X2 := superpose eq11 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq11 eq7
  have eq28 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = X2 := superpose eq22 eq21
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq28 eq7
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq33 eq33
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq45 eq36


@[equational_result]
theorem Equation9761_implies_Equation2 (G : Type*) [Magma G] (h : Equation9761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation9762_implies_Equation2 (G : Type*) [Magma G] (h : Equation9762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9763_implies_Equation2 (G : Type*) [Magma G] (h : Equation9763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9765_implies_Equation2 (G : Type*) [Magma G] (h : Equation9765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9766_implies_Equation2 (G : Type*) [Magma G] (h : Equation9766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation9767_implies_Equation2 (G : Type*) [Magma G] (h : Equation9767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9769_implies_Equation2 (G : Type*) [Magma G] (h : Equation9769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9770_implies_Equation2 (G : Type*) [Magma G] (h : Equation9770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9771_implies_Equation2 (G : Type*) [Magma G] (h : Equation9771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9772_implies_Equation2 (G : Type*) [Magma G] (h : Equation9772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9775_implies_Equation2 (G : Type*) [Magma G] (h : Equation9775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0))) = X3 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0))) = X3 := superpose eq12 eq13
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) = X3 := superpose eq12 eq15
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation9776_implies_Equation2 (G : Type*) [Magma G] (h : Equation9776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation9778_implies_Equation2 (G : Type*) [Magma G] (h : Equation9778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9779_implies_Equation2 (G : Type*) [Magma G] (h : Equation9779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9780_implies_Equation2 (G : Type*) [Magma G] (h : Equation9780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9782_implies_Equation2 (G : Type*) [Magma G] (h : Equation9782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9783_implies_Equation2 (G : Type*) [Magma G] (h : Equation9783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation9784_implies_Equation2 (G : Type*) [Magma G] (h : Equation9784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9786_implies_Equation2 (G : Type*) [Magma G] (h : Equation9786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9787_implies_Equation2 (G : Type*) [Magma G] (h : Equation9787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9788_implies_Equation2 (G : Type*) [Magma G] (h : Equation9788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9789_implies_Equation2 (G : Type*) [Magma G] (h : Equation9789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9791_implies_Equation2 (G : Type*) [Magma G] (h : Equation9791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation9792_implies_Equation2 (G : Type*) [Magma G] (h : Equation9792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation9793_implies_Equation2 (G : Type*) [Magma G] (h : Equation9793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X4 ◇ (X0 ◇ X4))) ◇ X0))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X3 ◇ X3) ◇ (X4 ◇ (X0 ◇ X4))) ◇ X0))) = X5 := superpose eq12 eq10
  have eq18 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (((X3 ◇ X3) ◇ (X4 ◇ (X0 ◇ X4))) ◇ X0)) = X5 := superpose eq12 eq14
  have eq19 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation9794_implies_Equation2 (G : Type*) [Magma G] (h : Equation9794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9796_implies_Equation2 (G : Type*) [Magma G] (h : Equation9796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9797_implies_Equation2 (G : Type*) [Magma G] (h : Equation9797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9798_implies_Equation2 (G : Type*) [Magma G] (h : Equation9798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9799_implies_Equation2 (G : Type*) [Magma G] (h : Equation9799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9801_implies_Equation2 (G : Type*) [Magma G] (h : Equation9801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9802_implies_Equation2 (G : Type*) [Magma G] (h : Equation9802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9803_implies_Equation2 (G : Type*) [Magma G] (h : Equation9803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9804_implies_Equation2 (G : Type*) [Magma G] (h : Equation9804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9806_implies_Equation2 (G : Type*) [Magma G] (h : Equation9806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9807_implies_Equation2 (G : Type*) [Magma G] (h : Equation9807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9808_implies_Equation2 (G : Type*) [Magma G] (h : Equation9808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9809_implies_Equation2 (G : Type*) [Magma G] (h : Equation9809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9811_implies_Equation2 (G : Type*) [Magma G] (h : Equation9811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9812_implies_Equation2 (G : Type*) [Magma G] (h : Equation9812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9813_implies_Equation2 (G : Type*) [Magma G] (h : Equation9813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9814_implies_Equation2 (G : Type*) [Magma G] (h : Equation9814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9815_implies_Equation2 (G : Type*) [Magma G] (h : Equation9815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9817_implies_Equation2 (G : Type*) [Magma G] (h : Equation9817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X5 ◇ X1)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq7 eq12
  have eq41 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = X5 := superpose eq26 eq9
  have eq52 (X1 X5 : G) : (X1 ◇ (X5 ◇ X1)) = X5 := superpose eq26 eq41
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq52 eq18
  have eq68 (X1 X5 : G) : (X1 ◇ X1) = X5 := superpose eq61 eq52
  have eq71 (X0 X2 : G) : X0 = X2 := superpose eq68 eq68
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq73 eq71


@[equational_result]
theorem Equation9818_implies_Equation2 (G : Type*) [Magma G] (h : Equation9818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X5 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X1 X2 X5 : G) : (X1 ◇ (X5 ◇ (X5 ◇ X2))) = X5 := superpose eq12 eq9
  have eq17 (X1 X2 X5 : G) : (X1 ◇ (X5 ◇ X2)) = X5 := superpose eq12 eq13
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq17 eq12
  have eq19 (X1 X5 : G) : (X1 ◇ X5) = X5 := superpose eq18 eq17
  have eq23 (X0 X1 : G) : X0 = X1 := superpose eq18 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation9819_implies_Equation2 (G : Type*) [Magma G] (h : Equation9819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X5 ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X0 ◇ X4))))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X0))) = X5 := superpose eq7 eq9
  have eq15 (X0 X1 X5 : G) : (X1 ◇ (X5 ◇ X0)) = X5 := superpose eq12 eq13
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) = X0 := superpose eq12 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq15 eq12
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X0 := superpose eq18 eq17
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq18 eq22
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation9820_implies_Equation2 (G : Type*) [Magma G] (h : Equation9820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X6 X7 : G) : (X1 ◇ (X0 ◇ (X6 ◇ (X6 ◇ X7)))) = X6 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X1 X6 X7 : G) : (X1 ◇ (X6 ◇ (X6 ◇ X7))) = X6 := superpose eq12 eq9
  have eq16 (X1 X6 X7 : G) : (X1 ◇ (X6 ◇ X7)) = X6 := superpose eq12 eq13
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq16 eq12
  have eq19 (X1 X6 : G) : (X1 ◇ X6) = X6 := superpose eq17 eq16
  have eq23 (X0 X1 : G) : X0 = X1 := superpose eq17 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation9822_implies_Equation2 (G : Type*) [Magma G] (h : Equation9822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X0)) = X1 := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ X0) := superpose eq10 eq7
  have eq36 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq29
  have eq128 (X0 X4 : G) : X0 = X4 := superpose eq7 eq36
  have eq235 (X0 : G) : sK0 ≠ X0 := superpose eq128 eq8
  subsumption eq235 eq128


@[equational_result]
theorem Equation9823_implies_Equation2 (G : Type*) [Magma G] (h : Equation9823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X1 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq12 eq7
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation9824_implies_Equation2 (G : Type*) [Magma G] (h : Equation9824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X1 ◇ ((X3 ◇ X4) ◇ (X0 ◇ (X2 ◇ X4))))))) = X5 := superpose eq7 eq7
  have eq34 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq53 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq34 eq34
  have eq114 (X0 X4 : G) : X0 = X4 := superpose eq7 eq53
  have eq241 (X0 : G) : sK0 ≠ X0 := superpose eq114 eq8
  subsumption eq241 eq114


@[equational_result]
theorem Equation9825_implies_Equation2 (G : Type*) [Magma G] (h : Equation9825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X3 ◇ X4) = (X0 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X5 : G) : (X5 ◇ X5) = X0 := superpose eq7 eq12
  have eq46 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq104 eq46


@[equational_result]
theorem Equation9827_implies_Equation2 (G : Type*) [Magma G] (h : Equation9827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X2 ◇ X1)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X4 ◇ (X5 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)))) = X5 := superpose eq12 eq9
  have eq40 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := superpose eq12 eq9
  have eq53 (X0 X3 X5 : G) : (X3 ◇ X0) = X5 := superpose eq40 eq37
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq53
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq134 eq54


@[equational_result]
theorem Equation9828_implies_Equation2 (G : Type*) [Magma G] (h : Equation9828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X2 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq9
  have eq51 (X1 X2 X5 : G) : (X1 ◇ X2) = X5 := superpose eq31 eq9
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq51 eq51
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq68 eq59


@[equational_result]
theorem Equation9829_implies_Equation2 (G : Type*) [Magma G] (h : Equation9829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq11
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq121 eq41


@[equational_result]
theorem Equation9830_implies_Equation2 (G : Type*) [Magma G] (h : Equation9830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 X4 : G) : (X3 ◇ X4) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation9832_implies_Equation2 (G : Type*) [Magma G] (h : Equation9832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (((X3 ◇ X4) ◇ (X0 ◇ (X4 ◇ X2))) ◇ X1)))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ (X1 ◇ (X4 ◇ X2))) ◇ (X5 ◇ (X0 ◇ X1)))) = X5 := superpose eq12 eq7
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ X1)) = (X0 ◇ ((X4 ◇ (X5 ◇ (X2 ◇ X3))) ◇ X1)) := superpose eq7 eq11
  have eq62 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (X2 ◇ X1)))) = X5 := superpose eq36 eq9
  have eq107 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ (X5 ◇ X0))) = X5 := superpose eq62 eq62
  have eq144 (X0 X2 X5 : G) : (X2 ◇ X0) = X5 := superpose eq107 eq29
  have eq145 (X0 X4 : G) : X0 = X4 := superpose eq7 eq144
  have eq292 (X0 : G) : sK0 ≠ X0 := superpose eq145 eq8
  subsumption eq292 eq145


@[equational_result]
theorem Equation9833_implies_Equation2 (G : Type*) [Magma G] (h : Equation9833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq54 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq71 eq54


@[equational_result]
theorem Equation9834_implies_Equation2 (G : Type*) [Magma G] (h : Equation9834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 : G) : (X4 ◇ (((X2 ◇ X3) ◇ (X0 ◇ (X3 ◇ X3))) ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X3 ◇ X3))))) = X0 := superpose eq7 eq11
  have eq29 (X0 X4 : G) : (X4 ◇ X0) = X0 := superpose eq7 eq14
  have eq30 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X3))) = X0 := superpose eq29 eq7
  have eq33 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = X0 := superpose eq29 eq30
  have eq34 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq29 eq33
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq37 eq35


@[equational_result]
theorem Equation9835_implies_Equation2 (G : Type*) [Magma G] (h : Equation9835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 X4 : G) : (X3 ◇ X4) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation9837_implies_Equation2 (G : Type*) [Magma G] (h : Equation9837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X5) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq36
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq133 eq57


@[equational_result]
theorem Equation9838_implies_Equation2 (G : Type*) [Magma G] (h : Equation9838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 X5 : G) : (X3 ◇ X5) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq139 eq49


@[equational_result]
theorem Equation9839_implies_Equation2 (G : Type*) [Magma G] (h : Equation9839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 X5 : G) : (X5 ◇ X4) = (X1 ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq47 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq131 eq47


@[equational_result]
theorem Equation9840_implies_Equation2 (G : Type*) [Magma G] (h : Equation9840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation9841_implies_Equation2 (G : Type*) [Magma G] (h : Equation9841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X4 := superpose eq7 eq7
  have eq39 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation9843_implies_Equation2 (G : Type*) [Magma G] (h : Equation9843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X5 ◇ X1)))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq7 eq11
  have eq32 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq22 eq7
  have eq37 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X5)) = X5 := superpose eq32 eq9
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq32 eq37
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq46 eq43


@[equational_result]
theorem Equation9844_implies_Equation2 (G : Type*) [Magma G] (h : Equation9844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X5 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq160 eq57


@[equational_result]
theorem Equation9845_implies_Equation2 (G : Type*) [Magma G] (h : Equation9845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X5 ◇ ((X3 ◇ X4) ◇ (X2 ◇ (X0 ◇ X4))))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X2) = (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X5 ◇ (X0 ◇ X4))))) := superpose eq7 eq12
  have eq35 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X5))) = X5 := superpose eq19 eq9
  have eq44 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq35
  have eq58 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) = X0 := superpose eq44 eq7
  have eq83 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq44 eq58
  have eq84 (X0 X3 : G) : X0 = X3 := superpose eq83 eq83
  have eq86 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq86 eq84


@[equational_result]
theorem Equation9846_implies_Equation2 (G : Type*) [Magma G] (h : Equation9846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq20
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq141 eq53


@[equational_result]
theorem Equation9848_implies_Equation2 (G : Type*) [Magma G] (h : Equation9848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9849_implies_Equation2 (G : Type*) [Magma G] (h : Equation9849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9850_implies_Equation2 (G : Type*) [Magma G] (h : Equation9850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9851_implies_Equation2 (G : Type*) [Magma G] (h : Equation9851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9853_implies_Equation2 (G : Type*) [Magma G] (h : Equation9853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9854_implies_Equation2 (G : Type*) [Magma G] (h : Equation9854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9855_implies_Equation2 (G : Type*) [Magma G] (h : Equation9855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9856_implies_Equation2 (G : Type*) [Magma G] (h : Equation9856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9858_implies_Equation2 (G : Type*) [Magma G] (h : Equation9858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9859_implies_Equation2 (G : Type*) [Magma G] (h : Equation9859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9860_implies_Equation2 (G : Type*) [Magma G] (h : Equation9860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9861_implies_Equation2 (G : Type*) [Magma G] (h : Equation9861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9863_implies_Equation2 (G : Type*) [Magma G] (h : Equation9863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9864_implies_Equation2 (G : Type*) [Magma G] (h : Equation9864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9865_implies_Equation2 (G : Type*) [Magma G] (h : Equation9865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9866_implies_Equation2 (G : Type*) [Magma G] (h : Equation9866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9867_implies_Equation2 (G : Type*) [Magma G] (h : Equation9867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9869_implies_Equation2 (G : Type*) [Magma G] (h : Equation9869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X1 := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq12
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq29
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq135 eq38


@[equational_result]
theorem Equation9870_implies_Equation2 (G : Type*) [Magma G] (h : Equation9870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2)))) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation9871_implies_Equation2 (G : Type*) [Magma G] (h : Equation9871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation9872_implies_Equation2 (G : Type*) [Magma G] (h : Equation9872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9874_implies_Equation2 (G : Type*) [Magma G] (h : Equation9874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9875_implies_Equation2 (G : Type*) [Magma G] (h : Equation9875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9876_implies_Equation2 (G : Type*) [Magma G] (h : Equation9876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9877_implies_Equation2 (G : Type*) [Magma G] (h : Equation9877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9879_implies_Equation2 (G : Type*) [Magma G] (h : Equation9879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9880_implies_Equation2 (G : Type*) [Magma G] (h : Equation9880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9881_implies_Equation2 (G : Type*) [Magma G] (h : Equation9881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation9882_implies_Equation2 (G : Type*) [Magma G] (h : Equation9882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9884_implies_Equation2 (G : Type*) [Magma G] (h : Equation9884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9885_implies_Equation2 (G : Type*) [Magma G] (h : Equation9885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9886_implies_Equation2 (G : Type*) [Magma G] (h : Equation9886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9887_implies_Equation2 (G : Type*) [Magma G] (h : Equation9887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9889_implies_Equation2 (G : Type*) [Magma G] (h : Equation9889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9890_implies_Equation2 (G : Type*) [Magma G] (h : Equation9890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9891_implies_Equation2 (G : Type*) [Magma G] (h : Equation9891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9892_implies_Equation2 (G : Type*) [Magma G] (h : Equation9892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9893_implies_Equation2 (G : Type*) [Magma G] (h : Equation9893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9895_implies_Equation2 (G : Type*) [Magma G] (h : Equation9895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq12 eq7
  have eq62 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq160 eq62


@[equational_result]
theorem Equation9896_implies_Equation2 (G : Type*) [Magma G] (h : Equation9896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation9897_implies_Equation2 (G : Type*) [Magma G] (h : Equation9897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq64 eq15


@[equational_result]
theorem Equation9898_implies_Equation2 (G : Type*) [Magma G] (h : Equation9898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation9900_implies_Equation2 (G : Type*) [Magma G] (h : Equation9900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9901_implies_Equation2 (G : Type*) [Magma G] (h : Equation9901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9902_implies_Equation2 (G : Type*) [Magma G] (h : Equation9902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9903_implies_Equation2 (G : Type*) [Magma G] (h : Equation9903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9905_implies_Equation2 (G : Type*) [Magma G] (h : Equation9905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9906_implies_Equation2 (G : Type*) [Magma G] (h : Equation9906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9907_implies_Equation2 (G : Type*) [Magma G] (h : Equation9907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9908_implies_Equation2 (G : Type*) [Magma G] (h : Equation9908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9910_implies_Equation2 (G : Type*) [Magma G] (h : Equation9910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9911_implies_Equation2 (G : Type*) [Magma G] (h : Equation9911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9912_implies_Equation2 (G : Type*) [Magma G] (h : Equation9912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9913_implies_Equation2 (G : Type*) [Magma G] (h : Equation9913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9915_implies_Equation2 (G : Type*) [Magma G] (h : Equation9915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9916_implies_Equation2 (G : Type*) [Magma G] (h : Equation9916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9917_implies_Equation2 (G : Type*) [Magma G] (h : Equation9917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9918_implies_Equation2 (G : Type*) [Magma G] (h : Equation9918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9919_implies_Equation2 (G : Type*) [Magma G] (h : Equation9919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9921_implies_Equation2 (G : Type*) [Magma G] (h : Equation9921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X5 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation9922_implies_Equation2 (G : Type*) [Magma G] (h : Equation9922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9923_implies_Equation2 (G : Type*) [Magma G] (h : Equation9923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation9924_implies_Equation2 (G : Type*) [Magma G] (h : Equation9924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9925_implies_Equation2 (G : Type*) [Magma G] (h : Equation9925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation9927_implies_Equation2 (G : Type*) [Magma G] (h : Equation9927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9928_implies_Equation2 (G : Type*) [Magma G] (h : Equation9928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9929_implies_Equation2 (G : Type*) [Magma G] (h : Equation9929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9930_implies_Equation2 (G : Type*) [Magma G] (h : Equation9930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9931_implies_Equation2 (G : Type*) [Magma G] (h : Equation9931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X1 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9933_implies_Equation2 (G : Type*) [Magma G] (h : Equation9933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9934_implies_Equation2 (G : Type*) [Magma G] (h : Equation9934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9935_implies_Equation2 (G : Type*) [Magma G] (h : Equation9935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation9936_implies_Equation2 (G : Type*) [Magma G] (h : Equation9936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9937_implies_Equation2 (G : Type*) [Magma G] (h : Equation9937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X2 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9939_implies_Equation2 (G : Type*) [Magma G] (h : Equation9939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9940_implies_Equation2 (G : Type*) [Magma G] (h : Equation9940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9941_implies_Equation2 (G : Type*) [Magma G] (h : Equation9941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9942_implies_Equation2 (G : Type*) [Magma G] (h : Equation9942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9943_implies_Equation2 (G : Type*) [Magma G] (h : Equation9943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X3 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9945_implies_Equation2 (G : Type*) [Magma G] (h : Equation9945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9946_implies_Equation2 (G : Type*) [Magma G] (h : Equation9946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9947_implies_Equation2 (G : Type*) [Magma G] (h : Equation9947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9948_implies_Equation2 (G : Type*) [Magma G] (h : Equation9948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation9949_implies_Equation2 (G : Type*) [Magma G] (h : Equation9949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9951_implies_Equation2 (G : Type*) [Magma G] (h : Equation9951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9952_implies_Equation2 (G : Type*) [Magma G] (h : Equation9952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9953_implies_Equation2 (G : Type*) [Magma G] (h : Equation9953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9954_implies_Equation2 (G : Type*) [Magma G] (h : Equation9954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9955_implies_Equation2 (G : Type*) [Magma G] (h : Equation9955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation9956_implies_Equation2 (G : Type*) [Magma G] (h : Equation9956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X5 ◇ X6)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10162_implies_Equation2 (G : Type*) [Magma G] (h : Equation10162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq10 eq9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq13 eq12
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation10165_implies_Equation2 (G : Type*) [Magma G] (h : Equation10165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq12
  have eq23 (X0 X1 : G) : X0 = X1 := superpose eq11 eq22
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq31 eq23


@[equational_result]
theorem Equation10167_implies_Equation2 (G : Type*) [Magma G] (h : Equation10167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq9 eq9
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq7 eq15
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq69 eq31


@[equational_result]
theorem Equation10168_implies_Equation2 (G : Type*) [Magma G] (h : Equation10168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq12
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq142 eq45


@[equational_result]
theorem Equation10169_implies_Equation2 (G : Type*) [Magma G] (h : Equation10169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq12 eq11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq13
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation10172_implies_Equation2 (G : Type*) [Magma G] (h : Equation10172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X1 ◇ ((((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq10 eq9
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq11 eq12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq10
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq14 eq13
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq14 eq16
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq14
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq11 eq18
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq27 eq19


@[equational_result]
theorem Equation10175_implies_Equation2 (G : Type*) [Magma G] (h : Equation10175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation10177_implies_Equation2 (G : Type*) [Magma G] (h : Equation10177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq9 eq9
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq7 eq14
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq62 eq28


@[equational_result]
theorem Equation10179_implies_Equation2 (G : Type*) [Magma G] (h : Equation10179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq37 eq12


@[equational_result]
theorem Equation10181_implies_Equation2 (G : Type*) [Magma G] (h : Equation10181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ ((X3 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq7
  have eq17 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) ◇ ((X3 ◇ X3) ◇ X0)) = X3 := superpose eq11 eq10
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq11 eq10
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) := superpose eq10 eq7
  have eq68 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq15 eq15
  have eq98 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq15 eq17
  have eq135 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq68
  have eq199 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq135 eq7
  have eq279 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X3))) = X0 := superpose eq7 eq30
  have eq355 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq10 eq279
  have eq362 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose eq17 eq279
  have eq363 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq11 eq279
  have eq405 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq362 eq98
  have eq418 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq362 eq199
  have eq532 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq363 eq362
  have eq537 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq532 eq405
  have eq572 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq532 eq418
  have eq653 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq532 eq572
  have eq654 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq15 eq653
  have eq656 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq654 eq135
  have eq667 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq656
  have eq668 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := superpose eq667 eq7
  have eq674 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X0) = X0 := superpose eq667 eq26
  have eq678 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq667 eq279
  have eq683 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq667 eq355
  have eq684 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq667 eq537
  have eq725 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq678 eq674
  have eq726 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq725 eq532
  have eq731 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq667 eq683
  have eq732 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq726 eq684
  have eq733 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq731 eq732
  have eq734 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq733 eq668
  have eq748 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq733 eq734
  have eq749 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq733 eq748
  have eq767 (X0 X2 : G) : X0 = X2 := superpose eq749 eq749
  have eq769 (X0 : G) : sK0 ≠ X0 := superpose eq767 eq8
  subsumption eq769 eq767


@[equational_result]
theorem Equation10182_implies_Equation2 (G : Type*) [Magma G] (h : Equation10182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq155 eq56


@[equational_result]
theorem Equation10183_implies_Equation2 (G : Type*) [Magma G] (h : Equation10183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq12 eq11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq15
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation10185_implies_Equation2 (G : Type*) [Magma G] (h : Equation10185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq10 eq10
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X1))) := superpose eq10 eq7
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq9
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((X2 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X2 := superpose eq10 eq20
  have eq26 (X0 X1 X3 : G) : (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1))) = X3 := superpose eq20 eq20
  have eq31 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq20 eq7
  have eq37 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ X0) ◇ ((X3 ◇ X2) ◇ X2))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq20 eq12
  have eq50 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq10 eq12
  have eq52 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq12
  have eq69 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq37
  have eq99 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X2 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq50 eq7
  have eq129 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq20 eq11
  have eq153 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := superpose eq11 eq12
  have eq171 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq31 eq129
  have eq179 (X0 X2 : G) : ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X2 := superpose eq171 eq24
  have eq192 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq171 eq99
  have eq235 (X0 X2 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X2 := superpose eq69 eq179
  have eq252 (X2 : G) : (X2 ◇ X2) = (X2 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq171 eq192
  have eq253 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq69 eq252
  have eq259 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq253 eq52
  have eq263 (X0 X2 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = X2 := superpose eq253 eq235
  have eq268 (X0 X1 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1))) = X3 := superpose eq253 eq26
  have eq291 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq253 eq259
  have eq301 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq253 eq263
  have eq302 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq253 eq301
  have eq315 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq253 eq268
  have eq316 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq253 eq315
  have eq317 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq302 eq316
  have eq530 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := superpose eq291 eq153
  have eq531 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq317 eq530
  have eq532 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq291 eq531
  have eq533 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq253 eq532
  have eq534 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq533 eq317
  have eq540 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq533 eq534
  have eq541 (X0 X3 : G) : X0 = X3 := superpose eq540 eq540
  have eq546 (X0 : G) : sK0 ≠ X0 := superpose eq541 eq8
  subsumption eq546 eq541


@[equational_result]
theorem Equation10187_implies_Equation2 (G : Type*) [Magma G] (h : Equation10187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq37 eq12


@[equational_result]
theorem Equation10189_implies_Equation2 (G : Type*) [Magma G] (h : Equation10189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation10190_implies_Equation2 (G : Type*) [Magma G] (h : Equation10190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10191_implies_Equation2 (G : Type*) [Magma G] (h : Equation10191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10193_implies_Equation2 (G : Type*) [Magma G] (h : Equation10193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq37 eq26


@[equational_result]
theorem Equation10194_implies_Equation2 (G : Type*) [Magma G] (h : Equation10194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq11 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq49 eq30


@[equational_result]
theorem Equation10195_implies_Equation2 (G : Type*) [Magma G] (h : Equation10195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq51 eq21


@[equational_result]
theorem Equation10196_implies_Equation2 (G : Type*) [Magma G] (h : Equation10196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation10199_implies_Equation2 (G : Type*) [Magma G] (h : Equation10199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq96 eq30


@[equational_result]
theorem Equation10202_implies_Equation2 (G : Type*) [Magma G] (h : Equation10202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq89 eq30


@[equational_result]
theorem Equation10204_implies_Equation2 (G : Type*) [Magma G] (h : Equation10204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1))))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))))) = X1 := superpose eq10 eq10
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X3 := superpose eq10 eq10
  have eq45 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq13
  have eq142 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq15 eq45
  have eq144 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X2) ◇ X2) := superpose eq15 eq10
  have eq151 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X1) = ((X0 ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X1) ◇ X5) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X1)))))) := superpose eq15 eq9
  have eq178 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) = X3 := superpose eq144 eq15
  have eq239 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) := superpose eq144 eq142
  have eq308 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X1) = ((X0 ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X3 ◇ X2))) := superpose eq144 eq151
  have eq309 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = ((X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1))) ◇ (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X2))) := superpose eq144 eq308
  have eq310 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = ((X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1))) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) := superpose eq144 eq309
  have eq311 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) := superpose eq239 eq310
  have eq312 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X3 := superpose eq311 eq178
  have eq343 (X0 X3 : G) : X0 = X3 := superpose eq312 eq312
  have eq350 (X0 : G) : sK0 ≠ X0 := superpose eq343 eq8
  subsumption eq350 eq343


@[equational_result]
theorem Equation10206_implies_Equation2 (G : Type*) [Magma G] (h : Equation10206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X4) ◇ X5))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X4) ◇ X5)) = X1 := superpose eq12 eq9
  have eq17 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X5) = X1 := superpose eq12 eq13
  have eq18 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X2) ◇ X3) ◇ X5) = X1 := superpose eq12 eq17
  have eq19 (X1 X3 X5 : G) : (X3 ◇ X5) = X1 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation10209_implies_Equation2 (G : Type*) [Magma G] (h : Equation10209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq117 eq37


@[equational_result]
theorem Equation10212_implies_Equation2 (G : Type*) [Magma G] (h : Equation10212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq98 eq31


@[equational_result]
theorem Equation10214_implies_Equation2 (G : Type*) [Magma G] (h : Equation10214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1))))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))))) = X1 := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X3 := superpose eq10 eq10
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) = ((X0 ◇ (X4 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X5 ◇ (X0 ◇ (X4 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))))))))) := superpose eq12 eq12
  have eq63 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq14 eq14
  have eq67 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)))) := superpose eq14 eq9
  have eq69 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X0))) := superpose eq14 eq12
  have eq70 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq14 eq10
  have eq81 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1)))) = X1 := superpose eq70 eq12
  have eq85 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X0))) = ((X0 ◇ (X4 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X5 ◇ (X0 ◇ (X4 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X0)))))))) := superpose eq70 eq35
  have eq112 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq70 eq67
  have eq113 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq69 eq85
  have eq115 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq113 eq81
  have eq154 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq115 eq70
  have eq166 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq154 eq112
  have eq169 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq166 eq63
  have eq172 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq166 eq70
  have eq185 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq166 eq154
  have eq192 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq172 eq169
  have eq211 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq185 eq166
  have eq219 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq211 eq192
  have eq231 (X0 X1 : G) : X0 = X1 := superpose eq211 eq219
  have eq241 (X0 : G) : sK0 ≠ X0 := superpose eq231 eq8
  subsumption eq241 eq231


@[equational_result]
theorem Equation10215_implies_Equation2 (G : Type*) [Magma G] (h : Equation10215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq10
  have eq40 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq17 eq7
  have eq82 (X0 X2 : G) : X0 = X2 := superpose eq40 eq40
  have eq203 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq203 eq82


@[equational_result]
theorem Equation10216_implies_Equation2 (G : Type*) [Magma G] (h : Equation10216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq37 eq13


@[equational_result]
theorem Equation10219_implies_Equation2 (G : Type*) [Magma G] (h : Equation10219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X0 ◇ ((X3 ◇ X1) ◇ X3))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) = (X1 ◇ ((((X0 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X1) ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X3)) = (((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) ◇ ((X4 ◇ X1) ◇ X4)) ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X5 ◇ X2) ◇ X5))))) := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X3)) = (((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) ◇ ((X4 ◇ X1) ◇ X4)) ◇ (X1 ◇ X2)) := superpose eq7 eq16
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X2)) = ((X1 ◇ ((X3 ◇ X0) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq10
  have eq67 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ ((X5 ◇ X3) ◇ X5)) = ((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) ◇ (((X4 ◇ X0) ◇ X4) ◇ (X3 ◇ ((X4 ◇ X0) ◇ X4)))) := superpose eq26 eq26
  have eq80 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := superpose eq9 eq26
  have eq126 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X3 ◇ X0) ◇ X3)) := superpose eq80 eq80
  have eq128 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)))) := superpose eq9 eq80
  have eq162 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X1) := superpose eq7 eq128
  have eq320 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ ((X4 ◇ X3) ◇ X4)))) = X0 := superpose eq21 eq80
  have eq333 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ ((X5 ◇ X3) ◇ X5)) = ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X4 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ ((X6 ◇ X4) ◇ X6)))) ◇ ((X4 ◇ X0) ◇ (X3 ◇ (X4 ◇ X0)))) := superpose eq21 eq26
  have eq346 (X0 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ X3) = X0 := superpose eq7 eq320
  have eq355 (X0 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ ((X5 ◇ X3) ◇ X5)) = ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ (X3 ◇ (X4 ◇ X0)))) := superpose eq7 eq333
  have eq382 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) = X2 := superpose eq346 eq7
  have eq397 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X2 ◇ X0) ◇ X2)) = X1 := superpose eq346 eq80
  have eq429 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X2) = X1 := superpose eq397 eq126
  have eq453 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ X1) := superpose eq429 eq162
  have eq512 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ ((X5 ◇ X3) ◇ X5)) = ((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) ◇ (((X4 ◇ X0) ◇ X4) ◇ (X4 ◇ X0))) := superpose eq453 eq67
  have eq516 (X0 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ ((X5 ◇ X3) ◇ X5)) = ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X4)) := superpose eq453 eq355
  have eq519 (X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X2)) = X2 := superpose eq453 eq382
  have eq586 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ ((X5 ◇ X3) ◇ X5)) = ((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X0 ◇ X2))) ◇ (((X4 ◇ X0) ◇ X4) ◇ (X4 ◇ X0))) := superpose eq453 eq512
  have eq587 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ ((X5 ◇ X3) ◇ X5)) = ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ (((X4 ◇ X0) ◇ X4) ◇ (X4 ◇ X0))) := superpose eq429 eq586
  have eq592 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X1 := superpose eq519 eq397
  have eq604 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X0) ◇ X4)) = ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ (((X4 ◇ X0) ◇ X4) ◇ (X4 ◇ X0))) := superpose eq592 eq587
  have eq605 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = ((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X4)) := superpose eq592 eq516
  have eq641 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ (((X4 ◇ X0) ◇ X4) ◇ (X4 ◇ X0))) = X3 := superpose eq592 eq604
  have eq642 (X0 X3 X4 : G) : (X3 ◇ X4) = (X3 ◇ (X4 ◇ X0)) := superpose eq592 eq605
  have eq643 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ (((X4 ◇ X0) ◇ X4) ◇ X4)) = X3 := superpose eq642 eq641
  have eq652 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) = X3 := superpose eq346 eq643
  have eq653 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq642 eq652
  have eq654 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = X3 := superpose eq642 eq653
  have eq657 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq654 eq519
  have eq664 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq657 eq654
  have eq665 (X0 X3 : G) : X0 = X3 := superpose eq664 eq664
  have eq667 (X0 : G) : sK0 ≠ X0 := superpose eq665 eq8
  subsumption eq667 eq665


@[equational_result]
theorem Equation10220_implies_Equation2 (G : Type*) [Magma G] (h : Equation10220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq127 eq42


@[equational_result]
theorem Equation10223_implies_Equation2 (G : Type*) [Magma G] (h : Equation10223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2))) ◇ X3))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) = (((X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3))) ◇ (X0 ◇ X2)) ◇ (X1 ◇ ((X4 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3))) ◇ (X0 ◇ X2))) ◇ X4))) := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq9
  have eq40 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq10
  have eq43 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X0) ◇ X3))))) = X2 := superpose eq15 eq7
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = X1 := superpose eq15 eq40
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) = X2 := superpose eq7 eq43
  have eq150 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) = ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))))) := superpose eq50 eq13
  have eq169 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) = X3 := superpose eq7 eq52
  have eq221 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq169
  have eq262 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) = ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))) := superpose eq221 eq150
  have eq311 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) = X1 := superpose eq221 eq221
  have eq350 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) = (X2 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)))) := superpose eq311 eq262
  have eq363 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) = X1 := superpose eq221 eq350
  have eq364 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq363 eq7
  have eq406 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X1 := superpose eq364 eq50
  have eq442 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq364 eq406
  have eq443 (X0 X3 : G) : X0 = X3 := superpose eq442 eq442
  have eq448 (X0 : G) : sK0 ≠ X0 := superpose eq443 eq8
  subsumption eq448 eq443


@[equational_result]
theorem Equation10224_implies_Equation2 (G : Type*) [Magma G] (h : Equation10224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq123 eq40


@[equational_result]
theorem Equation10226_implies_Equation2 (G : Type*) [Magma G] (h : Equation10226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X0 ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X1))))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)))) ◇ ((X3 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))))) ◇ X0)) = X3 := superpose eq9 eq7
  have eq20 (X0 X1 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X1 := superpose eq10 eq10
  have eq23 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq10 eq7
  have eq38 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq15 eq10
  have eq39 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X2)) = (((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0))))) := superpose eq15 eq9
  have eq41 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X0))) = ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq15 eq10
  have eq45 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq15 eq38
  have eq52 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq23 eq10
  have eq53 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))))))) := superpose eq23 eq9
  have eq55 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq45
  have eq68 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq55 eq20
  have eq73 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))))) := superpose eq55 eq39
  have eq75 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq55 eq45
  have eq79 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = X1 := superpose eq55 eq68
  have eq80 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X1 := superpose eq55 eq79
  have eq101 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq75 eq80
  have eq112 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq55 eq101
  have eq113 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq112 eq55
  have eq122 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)))) ◇ ((X3 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))))) ◇ X0)) = X3 := superpose eq113 eq16
  have eq131 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X0))) = ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq113 eq41
  have eq136 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq113 eq52
  have eq137 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))))))) := superpose eq113 eq53
  have eq140 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))))) = X2 := superpose eq113 eq73
  have eq170 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X3 ◇ ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X0)))) ◇ X0)) = X3 := superpose eq113 eq122
  have eq171 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ X0)) = X3 := superpose eq113 eq170
  have eq193 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X0))) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq113 eq131
  have eq194 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X3) ◇ X0)) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq113 eq193
  have eq195 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X3) ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq113 eq194
  have eq196 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) := superpose eq113 eq195
  have eq211 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq196 eq136
  have eq212 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq113 eq211
  have eq213 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))))))) := superpose eq196 eq137
  have eq214 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X0))))))) := superpose eq113 eq213
  have eq215 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))))))) := superpose eq113 eq214
  have eq216 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))))))) := superpose eq113 eq215
  have eq220 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)))) = X2 := superpose eq113 eq140
  have eq221 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0)))) = X2 := superpose eq113 eq220
  have eq222 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq221 eq216
  have eq223 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq222 eq212
  have eq225 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq113 eq223
  have eq228 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) = X3 := superpose eq225 eq171
  have eq257 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X3 := superpose eq225 eq228
  have eq258 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = X3 := superpose eq225 eq257
  have eq259 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq225 eq258
  have eq262 (X0 X2 : G) : X0 = X2 := superpose eq259 eq259
  have eq264 (X0 : G) : sK0 ≠ X0 := superpose eq262 eq8
  subsumption eq264 eq262


@[equational_result]
theorem Equation10227_implies_Equation2 (G : Type*) [Magma G] (h : Equation10227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X3 ◇ X3) ◇ X3))) = X1 := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) := superpose eq10 eq9
  have eq30 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq16
  have eq31 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq30 eq7
  have eq33 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq30 eq11
  have eq82 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq31 eq31
  have eq83 (X0 X1 : G) : X0 = X1 := superpose eq33 eq82
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq115 eq83


@[equational_result]
theorem Equation10228_implies_Equation2 (G : Type*) [Magma G] (h : Equation10228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq11 eq26
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq54 eq31


@[equational_result]
theorem Equation10230_implies_Equation2 (G : Type*) [Magma G] (h : Equation10230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X0 ◇ ((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))))) = X1 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq9
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq33
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq95 eq50


@[equational_result]
theorem Equation10231_implies_Equation2 (G : Type*) [Magma G] (h : Equation10231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq49 eq18


@[equational_result]
theorem Equation10232_implies_Equation2 (G : Type*) [Magma G] (h : Equation10232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq7 eq11
  have eq62 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq158 eq62


@[equational_result]
theorem Equation10233_implies_Equation2 (G : Type*) [Magma G] (h : Equation10233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation10235_implies_Equation2 (G : Type*) [Magma G] (h : Equation10235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq7 eq7
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq9 eq11
  have eq28 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) = X0 := superpose eq23 eq7
  have eq37 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq23 eq28
  have eq38 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq23 eq37
  have eq54 (X0 X2 : G) : X0 = X2 := superpose eq38 eq38
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq56 eq54


@[equational_result]
theorem Equation10236_implies_Equation2 (G : Type*) [Magma G] (h : Equation10236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X3) ◇ ((X0 ◇ X0) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq13
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq26 eq21


@[equational_result]
theorem Equation10237_implies_Equation2 (G : Type*) [Magma G] (h : Equation10237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq11 eq9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X2 := superpose eq13 eq11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation10239_implies_Equation2 (G : Type*) [Magma G] (h : Equation10239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X2 ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq7 eq9
  have eq20 (X0 X1 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) = X1 := superpose eq9 eq11
  have eq27 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq11 eq9
  have eq28 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq27 eq20
  have eq33 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq28 eq9
  have eq70 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq10 eq11
  have eq83 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq27 eq70
  have eq84 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq33 eq83
  have eq88 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq33 eq33
  have eq105 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) = X0 := superpose eq88 eq7
  have eq110 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq88 eq14
  have eq129 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq110 eq84
  have eq131 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq129 eq28
  have eq136 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X0 := superpose eq131 eq105
  have eq143 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq131 eq136
  have eq144 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq131 eq143
  have eq156 (X0 X2 : G) : X0 = X2 := superpose eq144 eq144
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq156 eq8
  subsumption eq158 eq156


@[equational_result]
theorem Equation10241_implies_Equation2 (G : Type*) [Magma G] (h : Equation10241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq11 eq9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X2 := superpose eq13 eq11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation10243_implies_Equation2 (G : Type*) [Magma G] (h : Equation10243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq38 eq18


@[equational_result]
theorem Equation10244_implies_Equation2 (G : Type*) [Magma G] (h : Equation10244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation10245_implies_Equation2 (G : Type*) [Magma G] (h : Equation10245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ X5)) = X2 := superpose eq12 eq9
  have eq15 (X1 X2 X5 : G) : (X1 ◇ X5) = X2 := superpose eq12 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation10247_implies_Equation2 (G : Type*) [Magma G] (h : Equation10247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X5) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq41 eq32


@[equational_result]
theorem Equation10248_implies_Equation2 (G : Type*) [Magma G] (h : Equation10248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X5) ◇ ((X0 ◇ X3) ◇ ((X0 ◇ X4) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq13
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation10249_implies_Equation2 (G : Type*) [Magma G] (h : Equation10249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ ((X0 ◇ X4) ◇ ((X0 ◇ X5) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq10
  have eq14 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq13 eq9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X2 := superpose eq14 eq13
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation10250_implies_Equation2 (G : Type*) [Magma G] (h : Equation10250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X6) ◇ X7))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X7 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq11 eq9
  have eq15 (X0 X1 X2 X7 : G) : (X1 ◇ (X0 ◇ X7)) = X2 := superpose eq13 eq10
  have eq17 (X1 X2 X7 : G) : (X1 ◇ X7) = X2 := superpose eq13 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation10252_implies_Equation2 (G : Type*) [Magma G] (h : Equation10252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq9 eq9
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq133 eq41


@[equational_result]
theorem Equation10253_implies_Equation2 (G : Type*) [Magma G] (h : Equation10253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X0) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) = (X1 ◇ ((((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ ((X2 ◇ ((X0 ◇ X4) ◇ (((X3 ◇ X2) ◇ X0) ◇ X4))) ◇ X0)))) = X3 := superpose eq7 eq9
  have eq113 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1))) = X2 := superpose eq10 eq7
  have eq150 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ X1))) = X0 := superpose eq7 eq18
  have eq316 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ X3)) = (((X1 ◇ X2) ◇ (((((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0) ◇ X1) ◇ X2))) := superpose eq7 eq113
  have eq383 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq7 eq150
  have eq440 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ X3)) = X1 := superpose eq383 eq316
  have eq448 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq440 eq7
  have eq1145 (X0 X2 : G) : X0 = X2 := superpose eq448 eq448
  have eq1147 (X0 : G) : sK0 ≠ X0 := superpose eq1145 eq8
  subsumption eq1147 eq1145


@[equational_result]
theorem Equation10254_implies_Equation2 (G : Type*) [Magma G] (h : Equation10254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq11 eq9
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation10256_implies_Equation2 (G : Type*) [Magma G] (h : Equation10256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq40 eq16


@[equational_result]
theorem Equation10257_implies_Equation2 (G : Type*) [Magma G] (h : Equation10257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X2) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq17 eq9
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq43 eq31


@[equational_result]
theorem Equation10258_implies_Equation2 (G : Type*) [Magma G] (h : Equation10258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10261_implies_Equation2 (G : Type*) [Magma G] (h : Equation10261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))))) = X1 := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ ((X4 ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X3) ◇ X3))))) ◇ (X0 ◇ ((X4 ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X3) ◇ X3))))))) = X4 := superpose eq7 eq9
  have eq38 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq11
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X2 ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))))) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))))))) := superpose eq38 eq12
  have eq107 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X2 ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq38 eq83
  have eq108 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq9 eq107
  have eq110 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X3) ◇ X2)) ◇ ((X0 ◇ X3) ◇ X2)))) = X2 := superpose eq108 eq9
  have eq158 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq108 eq110
  have eq208 (X0 X1 : G) : X0 = X1 := superpose eq38 eq158
  have eq228 (X0 : G) : sK0 ≠ X0 := superpose eq208 eq8
  subsumption eq228 eq208


@[equational_result]
theorem Equation10262_implies_Equation2 (G : Type*) [Magma G] (h : Equation10262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10264_implies_Equation2 (G : Type*) [Magma G] (h : Equation10264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X5) ◇ X1))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation10265_implies_Equation2 (G : Type*) [Magma G] (h : Equation10265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X5) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X4) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq10 eq9
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation10266_implies_Equation2 (G : Type*) [Magma G] (h : Equation10266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq48 eq12


@[equational_result]
theorem Equation10267_implies_Equation2 (G : Type*) [Magma G] (h : Equation10267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X6) ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq11 eq9
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation10270_implies_Equation2 (G : Type*) [Magma G] (h : Equation10270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X3) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2) ◇ ((X0 ◇ X3) ◇ ((X3 ◇ X0) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq57 eq17


@[equational_result]
theorem Equation10271_implies_Equation2 (G : Type*) [Magma G] (h : Equation10271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X3) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X2) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X5))) = X2 := superpose eq11 eq9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq28 eq17


@[equational_result]
theorem Equation10273_implies_Equation2 (G : Type*) [Magma G] (h : Equation10273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X3) ◇ ((X3 ◇ X2) ◇ X2)) ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ (((X3 ◇ ((((X3 ◇ X4) ◇ ((X4 ◇ X0) ◇ X0)) ◇ X2) ◇ X2)) ◇ X5) ◇ X5)) ◇ X1) ◇ X1))) = X5 := superpose eq9 eq9
  have eq28 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq10
  have eq50 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq28 eq7
  have eq109 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq50 eq7
  have eq161 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ X0) ◇ X0) = (X4 ◇ (X3 ◇ (((X2 ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) ◇ X4) ◇ X4))) := superpose eq28 eq12
  have eq199 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq109 eq10
  have eq201 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq109 eq7
  have eq229 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq201 eq199
  have eq230 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq229 eq50
  have eq232 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ (((X2 ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) ◇ X4) ◇ X4))) = X0 := superpose eq230 eq161
  have eq396 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X2 ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) ◇ X4) ◇ X4)) = X0 := superpose eq230 eq232
  have eq397 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq230 eq396
  have eq495 (X0 X1 : G) : X0 = X1 := superpose eq230 eq397
  have eq509 (X0 : G) : sK0 ≠ X0 := superpose eq495 eq8
  subsumption eq509 eq495


@[equational_result]
theorem Equation10275_implies_Equation2 (G : Type*) [Magma G] (h : Equation10275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X3) ◇ ((X3 ◇ X2) ◇ X4)) ◇ X1) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X5))) = X2 := superpose eq11 eq9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq28 eq17


@[equational_result]
theorem Equation10278_implies_Equation2 (G : Type*) [Magma G] (h : Equation10278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X3) ◇ ((X3 ◇ X3) ◇ X3)) ◇ ((X0 ◇ X3) ◇ ((X3 ◇ X3) ◇ X3))) ◇ ((X0 ◇ X3) ◇ ((X3 ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq31 eq20


@[equational_result]
theorem Equation10279_implies_Equation2 (G : Type*) [Magma G] (h : Equation10279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10281_implies_Equation2 (G : Type*) [Magma G] (h : Equation10281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X3 := superpose eq7 eq7
  have eq32 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq12 eq12
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq32
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq106 eq40


@[equational_result]
theorem Equation10282_implies_Equation2 (G : Type*) [Magma G] (h : Equation10282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X3) ◇ ((X3 ◇ X4) ◇ X3)) ◇ X5) ◇ ((X0 ◇ X3) ◇ ((X3 ◇ X4) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation10283_implies_Equation2 (G : Type*) [Magma G] (h : Equation10283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X3) ◇ ((X3 ◇ X4) ◇ X4)) ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ ((X0 ◇ X4) ◇ ((X4 ◇ X5) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X5) ◇ X5))) = X2 := superpose eq12 eq9
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq12 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation10284_implies_Equation2 (G : Type*) [Magma G] (h : Equation10284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ X3) ◇ ((X3 ◇ X4) ◇ X5)) ◇ X6) ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X6 X7 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X6) ◇ X7))) = X2 := superpose eq11 eq9
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation10286_implies_Equation2 (G : Type*) [Magma G] (h : Equation10286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ X2) ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq30 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq9 eq12
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq30
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq126 eq39


@[equational_result]
theorem Equation10287_implies_Equation2 (G : Type*) [Magma G] (h : Equation10287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation10288_implies_Equation2 (G : Type*) [Magma G] (h : Equation10288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ X2) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X1 X2 X5 : G) : (X1 ◇ X5) = X2 := superpose eq11 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation10289_implies_Equation2 (G : Type*) [Magma G] (h : Equation10289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X0 ◇ ((X6 ◇ X2) ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X6 : G) : (X1 ◇ X6) = X2 := superpose eq11 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation10291_implies_Equation2 (G : Type*) [Magma G] (h : Equation10291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation10292_implies_Equation2 (G : Type*) [Magma G] (h : Equation10292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ X1) ◇ ((X0 ◇ X3) ◇ ((X4 ◇ X2) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq22 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq155 eq53


@[equational_result]
theorem Equation10293_implies_Equation2 (G : Type*) [Magma G] (h : Equation10293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ X1) ◇ X5))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation10294_implies_Equation2 (G : Type*) [Magma G] (h : Equation10294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X0 ◇ ((X6 ◇ X1) ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X6 : G) : (X1 ◇ X6) = X2 := superpose eq11 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation10296_implies_Equation2 (G : Type*) [Magma G] (h : Equation10296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation10297_implies_Equation2 (G : Type*) [Magma G] (h : Equation10297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ ((X0 ◇ X3) ◇ ((X4 ◇ X3) ◇ X3))) ◇ ((X0 ◇ X3) ◇ ((X4 ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq31 eq20


@[equational_result]
theorem Equation10298_implies_Equation2 (G : Type*) [Magma G] (h : Equation10298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10299_implies_Equation2 (G : Type*) [Magma G] (h : Equation10299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10301_implies_Equation2 (G : Type*) [Magma G] (h : Equation10301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ X5) ◇ X1))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation10302_implies_Equation2 (G : Type*) [Magma G] (h : Equation10302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation10303_implies_Equation2 (G : Type*) [Magma G] (h : Equation10303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ ((X0 ◇ X4) ◇ ((X5 ◇ X5) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq10
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10304_implies_Equation2 (G : Type*) [Magma G] (h : Equation10304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10306_implies_Equation2 (G : Type*) [Magma G] (h : Equation10306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X0 ◇ ((X6 ◇ X7) ◇ X1))) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation10307_implies_Equation2 (G : Type*) [Magma G] (h : Equation10307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation10308_implies_Equation2 (G : Type*) [Magma G] (h : Equation10308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X0 ◇ ((X6 ◇ X7) ◇ X6))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X6 : G) : (X1 ◇ X6) = X2 := superpose eq11 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation10309_implies_Equation2 (G : Type*) [Magma G] (h : Equation10309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X0 ◇ ((X6 ◇ X7) ◇ X7))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ ((X0 ◇ X5) ◇ ((X6 ◇ X7) ◇ X7))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq10
  have eq14 (X1 X2 X6 : G) : (X1 ◇ X6) = X2 := superpose eq13 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation10310_implies_Equation2 (G : Type*) [Magma G] (h : Equation10310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X7 X8 X9 : G) : (X1 ◇ (X0 ◇ ((X7 ◇ X8) ◇ X9))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X7 : G) : (X1 ◇ X7) = X2 := superpose eq11 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation10313_implies_Equation2 (G : Type*) [Magma G] (h : Equation10313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq134 eq35


@[equational_result]
theorem Equation10316_implies_Equation2 (G : Type*) [Magma G] (h : Equation10316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq121 eq41


@[equational_result]
theorem Equation10318_implies_Equation2 (G : Type*) [Magma G] (h : Equation10318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) = (X1 ◇ (X0 ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2))) ◇ (((((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2))) ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq10 eq10
  have eq33 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X0)) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X0)) ◇ X4) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)))) = X4 := superpose eq9 eq10
  have eq38 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) ◇ (X4 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)))) = (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq7 eq13
  have eq48 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X1)) = X0 := superpose eq7 eq13
  have eq88 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X4 ◇ (X0 ◇ X1)))) := superpose eq13 eq10
  have eq135 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X0) ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X0) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))))) := superpose eq11 eq48
  have eq138 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := superpose eq13 eq48
  have eq171 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X0) ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) := superpose eq38 eq135
  have eq172 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2))) ◇ ((((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X0))) = X1 := superpose eq171 eq11
  have eq186 (X0 X1 X3 : G) : (X3 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq138 eq88
  have eq219 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (((((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X4) ◇ (X0 ◇ X1))) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))) ◇ ((((X2 ◇ (((((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X4) ◇ (X0 ◇ X1))) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))) ◇ (X2 ◇ X0))) = X2 := superpose eq9 eq172
  have eq259 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X2) := superpose eq7 eq186
  have eq373 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) = X0 := superpose eq7 eq259
  have eq491 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X0)) ◇ X1) = X4 := superpose eq373 eq33
  have eq492 (X0 X2 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq373 eq219
  have eq544 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq492 eq492
  have eq586 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq259 eq544
  have eq624 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X1) = X4 := superpose eq586 eq491
  have eq746 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq586 eq624
  have eq747 (X0 X1 : G) : X0 = X1 := superpose eq544 eq746
  have eq752 (X0 : G) : sK0 ≠ X0 := superpose eq747 eq8
  subsumption eq752 eq747


@[equational_result]
theorem Equation10319_implies_Equation2 (G : Type*) [Magma G] (h : Equation10319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) = (X1 ◇ (X0 ◇ (X3 ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ ((X3 ◇ X4) ◇ X4))))) := superpose eq7 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq10
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq17 eq17
  have eq83 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq17 eq37
  have eq159 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq83 eq17
  have eq161 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq83 eq7
  have eq177 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq83 eq17
  have eq193 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq83 eq177
  have eq222 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1))))) := superpose eq83 eq11
  have eq255 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq222
  have eq256 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq83 eq255
  have eq257 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq159 eq256
  have eq258 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq193 eq257
  have eq259 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq258 eq83
  have eq266 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq259 eq161
  have eq279 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq17 eq266
  have eq280 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq279 eq7
  have eq417 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq279 eq280
  have eq418 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq279 eq417
  have eq863 (X0 X2 : G) : X0 = X2 := superpose eq418 eq418
  have eq865 (X0 : G) : sK0 ≠ X0 := superpose eq863 eq8
  subsumption eq865 eq863


@[equational_result]
theorem Equation10320_implies_Equation2 (G : Type*) [Magma G] (h : Equation10320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq114 eq33


@[equational_result]
theorem Equation10323_implies_Equation2 (G : Type*) [Magma G] (h : Equation10323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq141 eq49


@[equational_result]
theorem Equation10326_implies_Equation2 (G : Type*) [Magma G] (h : Equation10326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq151 eq51


@[equational_result]
theorem Equation10328_implies_Equation2 (G : Type*) [Magma G] (h : Equation10328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = (X1 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X3) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0)))) := superpose eq9 eq9
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := superpose eq7 eq9
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X4) ◇ (X0 ◇ X1)))) := superpose eq9 eq7
  have eq40 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X0) ◇ ((((X0 ◇ X3) ◇ X0) ◇ X4) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))))) = X4 := superpose eq9 eq10
  have eq47 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0)))) = X1 := superpose eq32 eq30
  have eq53 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X3) ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq32
  have eq72 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X3) ◇ X0) := superpose eq53 eq37
  have eq76 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ X3) ◇ X1) := superpose eq7 eq72
  have eq128 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq7 eq76
  have eq220 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) = X0 := superpose eq47 eq128
  have eq309 (X0 X1 X3 X4 : G) : (((X0 ◇ X3) ◇ X0) ◇ X1) = X4 := superpose eq220 eq40
  have eq340 (X0 X4 : G) : X0 = X4 := superpose eq309 eq309
  have eq418 (X0 : G) : sK0 ≠ X0 := superpose eq340 eq8
  subsumption eq418 eq340


@[equational_result]
theorem Equation10330_implies_Equation2 (G : Type*) [Magma G] (h : Equation10330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq138 eq33


@[equational_result]
theorem Equation10332_implies_Equation2 (G : Type*) [Magma G] (h : Equation10332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1))) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ ((X3 ◇ X0) ◇ X2)) = (X1 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X0) ◇ X2))) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2))) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq9
  have eq22 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq18 eq7
  have eq24 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ X1))) := superpose eq18 eq10
  have eq31 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X2) ◇ X0)) = X2 := superpose eq18 eq11
  have eq35 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0))) = X1 := superpose eq22 eq22
  have eq36 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq22 eq22
  have eq43 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq35 eq35
  have eq59 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))) = (X0 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1)) := superpose eq22 eq18
  have eq63 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1))) := superpose eq22 eq18
  have eq68 (X0 X1 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))))) = ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq35 eq18
  have eq80 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) = (X0 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1)) := superpose eq18 eq59
  have eq81 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1)) := superpose eq22 eq80
  have eq114 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1))) = (((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X2)) ◇ ((((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X2)) ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1)))) ◇ X0)) := superpose eq35 eq24
  have eq127 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ X1)) = (((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X2)) ◇ ((((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ X1))) ◇ X0)) := superpose eq63 eq114
  have eq137 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq36 eq81
  have eq150 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq81 eq36
  have eq155 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1) := superpose eq36 eq150
  have eq166 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2)) := superpose eq36 eq31
  have eq170 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) ◇ ((((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) := superpose eq22 eq31
  have eq173 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq35 eq31
  have eq221 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq137 eq31
  have eq229 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq137 eq35
  have eq298 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) ◇ X0) := superpose eq18 eq155
  have eq325 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq22 eq298
  have eq326 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) := superpose eq325 eq170
  have eq327 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1))))) := superpose eq325 eq68
  have eq328 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ X1)) = (((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ X1))) ◇ X0)) := superpose eq325 eq127
  have eq342 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X2) ◇ X0)) = X2 := superpose eq325 eq31
  have eq359 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq325 eq221
  have eq363 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2)) := superpose eq325 eq166
  have eq375 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq325 eq173
  have eq382 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq326 eq43
  have eq390 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq325 eq342
  have eq414 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq325 eq359
  have eq416 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq325 eq375
  have eq417 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq326 eq416
  have eq418 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq417 eq382
  have eq419 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) = X1 := superpose eq418 eq35
  have eq426 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) := superpose eq418 eq326
  have eq427 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))))) := superpose eq418 eq327
  have eq428 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ X1)) = (((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ X1))) ◇ X0)) := superpose eq418 eq328
  have eq455 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)))) = X2 := superpose eq36 eq390
  have eq483 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X2 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)))) = X2 := superpose eq325 eq455
  have eq505 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3) = ((X3 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X2))) ◇ X3) := superpose eq24 eq325
  have eq507 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) := superpose eq36 eq325
  have eq515 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ X1)) := superpose eq325 eq325
  have eq557 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3))) = (X2 ◇ ((X2 ◇ (X3 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)))) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq325 eq24
  have eq581 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ X1)) = (((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq505 eq428
  have eq583 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ X1)) := superpose eq426 eq581
  have eq584 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq583 eq24
  have eq605 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))))) := superpose eq584 eq427
  have eq610 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq584 eq414
  have eq612 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq584 eq229
  have eq613 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)))) = X2 := superpose eq584 eq483
  have eq616 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) := superpose eq610 eq612
  have eq617 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq613 eq605
  have eq633 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X2)) := superpose eq507 eq363
  have eq662 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = ((((X2 ◇ X0) ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) := superpose eq515 eq616
  have eq709 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = (X3 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq325 eq584
  have eq777 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) = (X3 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq18 eq709
  have eq778 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) = X1 := superpose eq22 eq777
  have eq808 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = (X3 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3))) := superpose eq778 eq557
  have eq853 (X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) = (X3 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3))) := superpose eq18 eq808
  have eq854 (X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3))) = X1 := superpose eq22 eq853
  have eq857 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X2 := superpose eq854 eq613
  have eq872 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X2 := superpose eq857 eq662
  have eq875 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq872 eq36
  have eq915 (X0 X2 : G) : ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := superpose eq875 eq633
  have eq916 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq915 eq418
  have eq921 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X1 := superpose eq916 eq419
  have eq927 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq921 eq617
  have eq929 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq927 eq22
  have eq987 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq927 eq929
  have eq988 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq927 eq987
  have eq1029 (X0 X2 : G) : X0 = X2 := superpose eq988 eq988
  have eq1031 (X0 : G) : sK0 ≠ X0 := superpose eq1029 eq8
  subsumption eq1031 eq1029


@[equational_result]
theorem Equation10334_implies_Equation2 (G : Type*) [Magma G] (h : Equation10334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq17
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation10336_implies_Equation2 (G : Type*) [Magma G] (h : Equation10336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) = (X1 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1))))) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) ◇ ((X4 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1))) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)))) = (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1))))) := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq9
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = X1 := superpose eq26 eq24
  have eq38 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1)))) = (((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1)) ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1))))) := superpose eq10 eq10
  have eq60 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)))))) = X3 := superpose eq38 eq10
  have eq80 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X4 ◇ X0) ◇ X0)) := superpose eq9 eq26
  have eq96 (X0 X1 X3 X4 : G) : (X1 ◇ ((X3 ◇ X0) ◇ X0)) = (X1 ◇ ((X4 ◇ X0) ◇ X0)) := superpose eq7 eq80
  have eq140 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X1) ◇ X1)) = (X1 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) ◇ ((X4 ◇ X1) ◇ X1))) := superpose eq36 eq9
  have eq258 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq96
  have eq265 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X3 ◇ X0) ◇ X0)) = (X0 ◇ ((X4 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq9 eq96
  have eq359 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X3 ◇ X0) ◇ X0)) := superpose eq258 eq265
  have eq367 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X1) ◇ X1)) = (X1 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq359 eq140
  have eq537 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ X3) ◇ X3))) ◇ ((X3 ◇ X0) ◇ ((X4 ◇ X3) ◇ X3)))) = (((X3 ◇ X0) ◇ ((X4 ◇ X3) ◇ X3)) ◇ (X0 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ X3) ◇ X3)))) := superpose eq7 eq367
  have eq634 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1))))) = (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)))) := superpose eq537 eq19
  have eq636 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ (((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1))))) = X3 := superpose eq634 eq60
  have eq707 (X0 X4 : G) : X0 = X4 := superpose eq636 eq636
  have eq793 (X0 : G) : sK0 ≠ X0 := superpose eq707 eq8
  subsumption eq793 eq707


@[equational_result]
theorem Equation10338_implies_Equation2 (G : Type*) [Magma G] (h : Equation10338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq36 eq13


@[equational_result]
theorem Equation10341_implies_Equation2 (G : Type*) [Magma G] (h : Equation10341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = X0 := superpose eq11 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq11 eq15
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq20 eq20
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq20 eq26
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq64 eq27


@[equational_result]
theorem Equation10342_implies_Equation2 (G : Type*) [Magma G] (h : Equation10342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq11 eq7
  have eq20 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq14 eq11
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation10344_implies_Equation2 (G : Type*) [Magma G] (h : Equation10344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = (X1 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2))) ◇ (((((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2))) ◇ X5) ◇ X0)) = X5 := superpose eq7 eq7
  have eq42 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X4 ◇ X5) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0)))) := superpose eq9 eq9
  have eq44 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := superpose eq7 eq9
  have eq50 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X4 ◇ X5) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) ◇ ((X6 ◇ X7) ◇ (X0 ◇ X1)))) := superpose eq9 eq7
  have eq61 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0)))) = X1 := superpose eq44 eq42
  have eq67 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) ◇ ((X4 ◇ X5) ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq44
  have eq94 (X0 X1 X4 X5 : G) : ((X4 ◇ X5) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq67 eq50
  have eq128 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X5) ◇ (X1 ◇ X2))) ◇ X0) ◇ X3) = ((((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X5) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X3)) := superpose eq11 eq11
  have eq148 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2))) ◇ ((((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2))) ◇ (X5 ◇ X0))) = X5 := superpose eq128 eq11
  have eq184 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X4 ◇ X5) ◇ (X2 ◇ X3)))) = X0 := superpose eq94 eq7
  have eq247 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X0 ◇ X1) = ((((X4 ◇ X5) ◇ ((X6 ◇ X7) ◇ X0)) ◇ ((X8 ◇ X9) ◇ (X4 ◇ X5))) ◇ ((((X4 ◇ X5) ◇ ((X6 ◇ X7) ◇ X0)) ◇ ((X8 ◇ X9) ◇ (X4 ◇ X5))) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))))) := superpose eq9 eq148
  have eq372 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0))) = X4 := superpose eq44 eq61
  have eq409 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq372 eq247
  have eq410 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X4 ◇ X5) ◇ (X2 ◇ X3)))) = X0 := superpose eq409 eq184
  have eq517 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X0 := superpose eq409 eq410
  have eq518 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X0 := superpose eq409 eq517
  have eq519 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq409 eq518
  have eq532 (X0 X1 : G) : X0 = X1 := superpose eq409 eq519
  have eq534 (X0 : G) : sK0 ≠ X0 := superpose eq532 eq8
  subsumption eq534 eq532


@[equational_result]
theorem Equation10345_implies_Equation2 (G : Type*) [Magma G] (h : Equation10345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10346_implies_Equation2 (G : Type*) [Magma G] (h : Equation10346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq84 eq18


@[equational_result]
theorem Equation10347_implies_Equation2 (G : Type*) [Magma G] (h : Equation10347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation10350_implies_Equation2 (G : Type*) [Magma G] (h : Equation10350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq43 eq27


@[equational_result]
theorem Equation10353_implies_Equation2 (G : Type*) [Magma G] (h : Equation10353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation10355_implies_Equation2 (G : Type*) [Magma G] (h : Equation10355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation10357_implies_Equation2 (G : Type*) [Magma G] (h : Equation10357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq46 eq29


@[equational_result]
theorem Equation10360_implies_Equation2 (G : Type*) [Magma G] (h : Equation10360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq62 eq15


@[equational_result]
theorem Equation10362_implies_Equation2 (G : Type*) [Magma G] (h : Equation10362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation10363_implies_Equation2 (G : Type*) [Magma G] (h : Equation10363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation10365_implies_Equation2 (G : Type*) [Magma G] (h : Equation10365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10366_implies_Equation2 (G : Type*) [Magma G] (h : Equation10366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10367_implies_Equation2 (G : Type*) [Magma G] (h : Equation10367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10369_implies_Equation2 (G : Type*) [Magma G] (h : Equation10369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2)))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X2)) = (X5 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq9 eq9
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X3) = (X2 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X2))) := superpose eq9 eq7
  have eq34 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X1 := superpose eq24 eq23
  have eq39 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X3) = (X2 ◇ (X1 ◇ X0)) := superpose eq24 eq29
  have eq42 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ X4) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ X4))) ◇ (((((X3 ◇ X4) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ X4))) ◇ (((X3 ◇ X4) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ X4)))) ◇ ((X5 ◇ X5) ◇ (X2 ◇ X5)))) = X4 := superpose eq9 eq10
  have eq49 (X0 X1 X2 X3 : G) : (((((X2 ◇ X1) ◇ X3) ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((((((X2 ◇ X1) ◇ X3) ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((((X2 ◇ X1) ◇ X3) ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) ◇ X3)) = X3 := superpose eq9 eq10
  have eq60 (X0 X2 X4 X5 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X5 ◇ X5) ◇ (X2 ◇ X5)))) = X4 := superpose eq24 eq42
  have eq64 (X1 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X3)) = X3 := superpose eq34 eq49
  have eq70 (X0 X1 X5 : G) : (X5 ◇ (X1 ◇ X0)) = X1 := superpose eq64 eq34
  have eq85 (X0 X2 X4 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = X4 := superpose eq70 eq60
  have eq87 (X1 X3 X4 : G) : ((X4 ◇ X1) ◇ X3) = X1 := superpose eq70 eq39
  have eq100 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq87 eq85
  have eq105 (X0 X2 : G) : X0 = X2 := superpose eq100 eq100
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq121 eq105


@[equational_result]
theorem Equation10371_implies_Equation2 (G : Type*) [Magma G] (h : Equation10371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq46 eq29


@[equational_result]
theorem Equation10373_implies_Equation2 (G : Type*) [Magma G] (h : Equation10373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10374_implies_Equation2 (G : Type*) [Magma G] (h : Equation10374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10375_implies_Equation2 (G : Type*) [Magma G] (h : Equation10375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10377_implies_Equation2 (G : Type*) [Magma G] (h : Equation10377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10378_implies_Equation2 (G : Type*) [Magma G] (h : Equation10378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation10379_implies_Equation2 (G : Type*) [Magma G] (h : Equation10379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10381_implies_Equation2 (G : Type*) [Magma G] (h : Equation10381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10382_implies_Equation2 (G : Type*) [Magma G] (h : Equation10382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10383_implies_Equation2 (G : Type*) [Magma G] (h : Equation10383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10384_implies_Equation2 (G : Type*) [Magma G] (h : Equation10384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10386_implies_Equation2 (G : Type*) [Magma G] (h : Equation10386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X3) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X3) ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X3 ◇ X0)) = X1 := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = (X1 ◇ X0) := superpose eq10 eq9
  have eq32 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X0)) = X1 := superpose eq29 eq11
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq32 eq7
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq9 eq36
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq48 eq37


@[equational_result]
theorem Equation10387_implies_Equation2 (G : Type*) [Magma G] (h : Equation10387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ ((X0 ◇ X0) ◇ X3))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq9
  have eq32 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq15 eq15
  have eq40 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1))) = X0 := superpose eq15 eq10
  have eq52 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)))) = X3 := superpose eq32 eq9
  have eq66 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X3 := superpose eq32 eq52
  have eq81 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq66 eq40
  have eq93 (X0 X1 : G) : X0 = X1 := superpose eq15 eq81
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq93 eq8
  subsumption eq121 eq93


@[equational_result]
theorem Equation10388_implies_Equation2 (G : Type*) [Magma G] (h : Equation10388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq56 eq38


@[equational_result]
theorem Equation10390_implies_Equation2 (G : Type*) [Magma G] (h : Equation10390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X1))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X2 := superpose eq9 eq9
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq92 eq56


@[equational_result]
theorem Equation10392_implies_Equation2 (G : Type*) [Magma G] (h : Equation10392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation10396_implies_Equation2 (G : Type*) [Magma G] (h : Equation10396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation10398_implies_Equation2 (G : Type*) [Magma G] (h : Equation10398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq51 eq30


@[equational_result]
theorem Equation10399_implies_Equation2 (G : Type*) [Magma G] (h : Equation10399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X5) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2))))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X4 := superpose eq12 eq9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq13 eq10
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation10400_implies_Equation2 (G : Type*) [Magma G] (h : Equation10400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X5))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X4) ◇ ((X0 ◇ X5) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq9 eq10
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq57 eq39


@[equational_result]
theorem Equation10401_implies_Equation2 (G : Type*) [Magma G] (h : Equation10401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation10403_implies_Equation2 (G : Type*) [Magma G] (h : Equation10403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X1))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq9 eq9
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq113 eq55


@[equational_result]
theorem Equation10404_implies_Equation2 (G : Type*) [Magma G] (h : Equation10404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X3) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ ((X1 ◇ X0) ◇ X3)) = (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq9
  have eq21 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq9 eq9
  have eq76 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq20 eq10
  have eq78 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq20 eq7
  have eq82 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1))))) = X0 := superpose eq20 eq9
  have eq106 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq78 eq76
  have eq107 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq106 eq78
  have eq110 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq82
  have eq111 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq107 eq110
  have eq112 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq111 eq21
  have eq168 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq111 eq112
  have eq170 (X0 X2 : G) : X0 = X2 := superpose eq168 eq168
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq170 eq8
  subsumption eq172 eq170


@[equational_result]
theorem Equation10405_implies_Equation2 (G : Type*) [Magma G] (h : Equation10405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation10407_implies_Equation2 (G : Type*) [Magma G] (h : Equation10407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10408_implies_Equation2 (G : Type*) [Magma G] (h : Equation10408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10409_implies_Equation2 (G : Type*) [Magma G] (h : Equation10409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10411_implies_Equation2 (G : Type*) [Magma G] (h : Equation10411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation10412_implies_Equation2 (G : Type*) [Magma G] (h : Equation10412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation10413_implies_Equation2 (G : Type*) [Magma G] (h : Equation10413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10415_implies_Equation2 (G : Type*) [Magma G] (h : Equation10415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10416_implies_Equation2 (G : Type*) [Magma G] (h : Equation10416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10417_implies_Equation2 (G : Type*) [Magma G] (h : Equation10417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10418_implies_Equation2 (G : Type*) [Magma G] (h : Equation10418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10422_implies_Equation2 (G : Type*) [Magma G] (h : Equation10422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq63 eq18


@[equational_result]
theorem Equation10424_implies_Equation2 (G : Type*) [Magma G] (h : Equation10424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10425_implies_Equation2 (G : Type*) [Magma G] (h : Equation10425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10426_implies_Equation2 (G : Type*) [Magma G] (h : Equation10426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10428_implies_Equation2 (G : Type*) [Magma G] (h : Equation10428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10429_implies_Equation2 (G : Type*) [Magma G] (h : Equation10429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10430_implies_Equation2 (G : Type*) [Magma G] (h : Equation10430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10432_implies_Equation2 (G : Type*) [Magma G] (h : Equation10432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10433_implies_Equation2 (G : Type*) [Magma G] (h : Equation10433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10434_implies_Equation2 (G : Type*) [Magma G] (h : Equation10434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10435_implies_Equation2 (G : Type*) [Magma G] (h : Equation10435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10437_implies_Equation2 (G : Type*) [Magma G] (h : Equation10437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X1))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X3 := superpose eq7 eq9
  have eq81 (X0 X4 : G) : X0 = X4 := superpose eq16 eq16
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq168 eq81


@[equational_result]
theorem Equation10438_implies_Equation2 (G : Type*) [Magma G] (h : Equation10438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation10439_implies_Equation2 (G : Type*) [Magma G] (h : Equation10439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation10440_implies_Equation2 (G : Type*) [Magma G] (h : Equation10440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10442_implies_Equation2 (G : Type*) [Magma G] (h : Equation10442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10443_implies_Equation2 (G : Type*) [Magma G] (h : Equation10443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10444_implies_Equation2 (G : Type*) [Magma G] (h : Equation10444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10445_implies_Equation2 (G : Type*) [Magma G] (h : Equation10445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10447_implies_Equation2 (G : Type*) [Magma G] (h : Equation10447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10448_implies_Equation2 (G : Type*) [Magma G] (h : Equation10448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10449_implies_Equation2 (G : Type*) [Magma G] (h : Equation10449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10450_implies_Equation2 (G : Type*) [Magma G] (h : Equation10450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10452_implies_Equation2 (G : Type*) [Magma G] (h : Equation10452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10453_implies_Equation2 (G : Type*) [Magma G] (h : Equation10453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10454_implies_Equation2 (G : Type*) [Magma G] (h : Equation10454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10455_implies_Equation2 (G : Type*) [Magma G] (h : Equation10455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10457_implies_Equation2 (G : Type*) [Magma G] (h : Equation10457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10458_implies_Equation2 (G : Type*) [Magma G] (h : Equation10458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10459_implies_Equation2 (G : Type*) [Magma G] (h : Equation10459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10460_implies_Equation2 (G : Type*) [Magma G] (h : Equation10460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10461_implies_Equation2 (G : Type*) [Magma G] (h : Equation10461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10463_implies_Equation2 (G : Type*) [Magma G] (h : Equation10463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((((X3 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) ◇ ((X3 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (((((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq11 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq11 eq7
  have eq66 (X0 X1 X2 : G) : (((((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2))) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2))) = X1 := superpose eq9 eq15
  have eq67 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq15
  have eq81 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq67
  have eq97 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq81 eq14
  have eq112 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq81 eq97
  have eq113 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq112 eq7
  have eq117 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq112 eq12
  have eq120 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq112 eq15
  have eq149 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))) ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))) = X1 := superpose eq112 eq66
  have eq170 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq112 eq117
  have eq225 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X1 := superpose eq112 eq149
  have eq226 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X1 := superpose eq112 eq225
  have eq227 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq226 eq170
  have eq228 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq227 eq113
  have eq253 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq228 eq120
  have eq265 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq228 eq253
  have eq357 (X0 X1 : G) : X0 = X1 := superpose eq228 eq265
  have eq376 (X0 : G) : sK0 ≠ X0 := superpose eq357 eq8
  subsumption eq376 eq357


@[equational_result]
theorem Equation10464_implies_Equation2 (G : Type*) [Magma G] (h : Equation10464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X0)) = X3 := superpose eq12 eq11
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq15
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation10465_implies_Equation2 (G : Type*) [Magma G] (h : Equation10465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X0) ◇ X4)) = (X1 ◇ (X0 ◇ ((((X3 ◇ X0) ◇ ((X0 ◇ X0) ◇ X4)) ◇ ((X3 ◇ X0) ◇ ((X0 ◇ X0) ◇ X4))) ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X0) ◇ X4)) = (X1 ◇ (X0 ◇ (X0 ◇ X5))) := superpose eq7 eq9
  have eq15 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X5))) = X0 := superpose eq11 eq13
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X5)) = X0 := superpose eq16 eq15
  have eq19 (X0 X1 X5 : G) : (X1 ◇ X5) = X0 := superpose eq16 eq17
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation10467_implies_Equation2 (G : Type*) [Magma G] (h : Equation10467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) = (X1 ◇ (X0 ◇ ((((X3 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3)) = (X4 ◇ (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3)) ◇ X4) ◇ X4))) := superpose eq7 eq9
  have eq28 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq10
  have eq33 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) = (((X3 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0))))))) := superpose eq10 eq9
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq28 eq28
  have eq46 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq28 eq7
  have eq51 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((((X3 ◇ X0) ◇ X0) ◇ X1) ◇ X1))) := superpose eq28 eq7
  have eq58 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq28 eq9
  have eq60 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq28 eq43
  have eq62 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq46 eq60
  have eq64 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq46 eq28
  have eq79 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq46 eq58
  have eq102 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq46 eq7
  have eq112 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq46 eq9
  have eq118 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq51 eq112
  have eq119 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq46 eq118
  have eq209 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))))))) := superpose eq46 eq33
  have eq228 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))))) := superpose eq46 eq209
  have eq234 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq119 eq102
  have eq250 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq119 eq64
  have eq254 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X2 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq234 eq228
  have eq257 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X2 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq102 eq254
  have eq258 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq64 eq257
  have eq269 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq119 eq250
  have eq270 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq258 eq269
  have eq272 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq270 eq62
  have eq280 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq270 eq79
  have eq283 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq270 eq102
  have eq329 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq283 eq280
  have eq333 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ X0) ◇ X0) := superpose eq270 eq329
  have eq334 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq272 eq333
  have eq335 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X0 := superpose eq334 eq7
  have eq338 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ X3)) = (X4 ◇ (((X2 ◇ X0) ◇ X1) ◇ (((X0 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ X3)) ◇ X4) ◇ X4))) := superpose eq334 eq11
  have eq412 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ X3)) = (X4 ◇ (((X2 ◇ X0) ◇ X1) ◇ X4)) := superpose eq334 eq338
  have eq413 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X2 ◇ X0) ◇ X1) ◇ X3) ◇ X3)) = X1 := superpose eq335 eq412
  have eq414 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq334 eq413
  have eq417 (X0 X3 : G) : X0 = X3 := superpose eq335 eq414
  have eq454 (X0 : G) : sK0 ≠ X0 := superpose eq417 eq8
  subsumption eq454 eq417


@[equational_result]
theorem Equation10469_implies_Equation2 (G : Type*) [Magma G] (h : Equation10469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X2) ◇ X4)) = (X1 ◇ (X0 ◇ ((((X3 ◇ X0) ◇ ((X0 ◇ X2) ◇ X4)) ◇ X1) ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X5))) = X2 := superpose eq11 eq9
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq11 eq14
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq28 eq17


@[equational_result]
theorem Equation10471_implies_Equation2 (G : Type*) [Magma G] (h : Equation10471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X3) ◇ X2)) = (X1 ◇ (X0 ◇ ((((X3 ◇ X0) ◇ ((X0 ◇ X3) ◇ X2)) ◇ X2) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ ((X3 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := superpose eq7 eq12
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq12 eq12
  have eq18 (X0 X1 X3 : G) : (X1 ◇ ((((X0 ◇ X0) ◇ X3) ◇ X3) ◇ (X0 ◇ X1))) = X3 := superpose eq13 eq10
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ X1))) := superpose eq13 eq9
  have eq20 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq13 eq7
  have eq21 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X2) ◇ X0)) = X2 := superpose eq13 eq11
  have eq22 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq20 eq20
  have eq35 (X0 X1 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq20 eq18
  have eq70 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq21 eq20
  have eq78 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq70
  have eq85 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq78 eq35
  have eq88 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq85 eq70
  have eq90 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq88 eq14
  have eq91 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1))) := superpose eq88 eq19
  have eq93 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X2) ◇ X0)) = X2 := superpose eq88 eq21
  have eq123 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq88 eq90
  have eq205 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq88 eq91
  have eq220 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq123 eq205
  have eq224 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X2 := superpose eq220 eq93
  have eq256 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X2)) = X2 := superpose eq220 eq224
  have eq257 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq220 eq256
  have eq258 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq220 eq257
  have eq259 (X0 X1 : G) : X0 = X1 := superpose eq88 eq258
  have eq273 (X0 : G) : sK0 ≠ X0 := superpose eq259 eq8
  subsumption eq273 eq259


@[equational_result]
theorem Equation10472_implies_Equation2 (G : Type*) [Magma G] (h : Equation10472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ ((((X3 ◇ X0) ◇ ((X0 ◇ X3) ◇ X3)) ◇ X2) ◇ X2)) ◇ X4) ◇ ((X3 ◇ X0) ◇ ((X0 ◇ X3) ◇ X3)))) = X4 := superpose eq7 eq12
  have eq28 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq13
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq7 eq28
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq99 eq54


@[equational_result]
theorem Equation10473_implies_Equation2 (G : Type*) [Magma G] (h : Equation10473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X3) ◇ X4)) = (X1 ◇ (X0 ◇ ((((X3 ◇ X0) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X2) ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X5))) = X3 := superpose eq11 eq9
  have eq16 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq28 eq17


@[equational_result]
theorem Equation10475_implies_Equation2 (G : Type*) [Magma G] (h : Equation10475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq30 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X4) ◇ (X1 ◇ X2)) := superpose eq7 eq12
  have eq44 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = X3 := superpose eq30 eq12
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq44 eq44
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq60 eq48


@[equational_result]
theorem Equation10476_implies_Equation2 (G : Type*) [Magma G] (h : Equation10476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation10477_implies_Equation2 (G : Type*) [Magma G] (h : Equation10477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X4) ◇ X4)) = (X1 ◇ (X0 ◇ ((((X3 ◇ X0) ◇ ((X0 ◇ X4) ◇ X4)) ◇ X5) ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ ((X4 ◇ X0) ◇ ((X0 ◇ X5) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq13 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X5))) = X4 := superpose eq12 eq9
  have eq15 (X1 X4 X5 : G) : (X1 ◇ X5) = X4 := superpose eq12 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation10478_implies_Equation2 (G : Type*) [Magma G] (h : Equation10478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 X6 X7 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X4) ◇ X5)) = (X1 ◇ (X0 ◇ ((((X3 ◇ X0) ◇ ((X0 ◇ X4) ◇ X5)) ◇ X6) ◇ X7))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X6 X7 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X6) ◇ X7))) = X4 := superpose eq11 eq9
  have eq15 (X1 X4 X6 : G) : (X1 ◇ X6) = X4 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation10480_implies_Equation2 (G : Type*) [Magma G] (h : Equation10480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X1 ◇ ((X3 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq11 eq11
  have eq14 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose eq11 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq7 eq9
  have eq29 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq23 eq7
  have eq42 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq13 eq11
  have eq44 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq11 eq29
  have eq45 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq13 eq29
  have eq49 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq44
  have eq51 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq49 eq14
  have eq52 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq49 eq11
  have eq54 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq13 eq45
  have eq55 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq54 eq42
  have eq69 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq52 eq15
  have eq75 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq54 eq69
  have eq76 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq75 eq55
  have eq77 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq75 eq51
  have eq80 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq76 eq54
  have eq81 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq80 eq52
  have eq82 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq80 eq49
  have eq85 (X0 X2 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq81 eq77
  have eq86 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq81 eq85
  have eq108 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq86 eq15
  have eq113 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq81 eq108
  have eq114 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq86 eq113
  have eq118 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq114 eq82
  have eq153 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq118 eq118
  have eq166 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq114 eq153
  have eq167 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq166 eq15
  have eq204 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq166 eq167
  have eq274 (X0 X2 : G) : X0 = X2 := superpose eq204 eq204
  have eq279 (X0 : G) : sK0 ≠ X0 := superpose eq274 eq8
  subsumption eq279 eq274


@[equational_result]
theorem Equation10482_implies_Equation2 (G : Type*) [Magma G] (h : Equation10482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ X4)) = (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ X4))) ◇ (X0 ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ X4)) = (X1 ◇ (X0 ◇ (X0 ◇ X5))) := superpose eq11 eq10
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X5))) = X0 := superpose eq11 eq13
  have eq18 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X5)) = X0 := superpose eq15 eq16
  have eq20 (X0 X1 X5 : G) : (X1 ◇ X5) = X0 := superpose eq15 eq18
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq26 eq21


@[equational_result]
theorem Equation10484_implies_Equation2 (G : Type*) [Magma G] (h : Equation10484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq9
  have eq54 (X0 X1 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose eq9 eq10
  have eq65 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq7 eq54
  have eq66 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) = X0 := superpose eq65 eq7
  have eq67 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq65 eq9
  have eq71 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq65 eq21
  have eq83 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X0 := superpose eq65 eq66
  have eq84 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) = (X1 ◇ (X0 ◇ X1)) := superpose eq65 eq67
  have eq85 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq65 eq84
  have eq86 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X2) := superpose eq65 eq85
  have eq99 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq65 eq71
  have eq100 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq65 eq99
  have eq101 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq65 eq100
  have eq102 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq65 eq101
  have eq103 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq102 eq86
  have eq104 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq102 eq83
  have eq108 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq104 eq103
  have eq127 (X0 X1 : G) : X0 = X1 := superpose eq104 eq108
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq127 eq8
  subsumption eq132 eq127


@[equational_result]
theorem Equation10486_implies_Equation2 (G : Type*) [Magma G] (h : Equation10486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10490_implies_Equation2 (G : Type*) [Magma G] (h : Equation10490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10492_implies_Equation2 (G : Type*) [Magma G] (h : Equation10492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation10493_implies_Equation2 (G : Type*) [Magma G] (h : Equation10493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq10 eq10
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq168 eq65


@[equational_result]
theorem Equation10494_implies_Equation2 (G : Type*) [Magma G] (h : Equation10494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ ((X4 ◇ X0) ◇ ((X1 ◇ X5) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X0) ◇ (((X2 ◇ X3) ◇ X5) ◇ X5)))) = X3 := superpose eq7 eq11
  have eq23 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X3 := superpose eq11 eq14
  have eq25 (X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X5) ◇ X5))) = X3 := superpose eq23 eq10
  have eq27 (X1 X3 X5 : G) : (X1 ◇ X5) = X3 := superpose eq23 eq25
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq27
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation10495_implies_Equation2 (G : Type*) [Magma G] (h : Equation10495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10497_implies_Equation2 (G : Type*) [Magma G] (h : Equation10497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq7
  have eq17 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq9
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq17 eq7
  have eq25 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq19 eq17
  have eq27 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq19 eq25
  have eq29 (X0 X1 : G) : X0 = X1 := superpose eq19 eq27
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation10498_implies_Equation2 (G : Type*) [Magma G] (h : Equation10498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ X3)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) = ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) := superpose eq9 eq9
  have eq30 (X1 X2 : G) : ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X1 := superpose eq7 eq22
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq30 eq7
  have eq32 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq30 eq9
  have eq52 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq31 eq32
  have eq53 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq31 eq52
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq53 eq53
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq59 eq54


@[equational_result]
theorem Equation10499_implies_Equation2 (G : Type*) [Magma G] (h : Equation10499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ X4)) = (X1 ◇ (X0 ◇ (X0 ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X5))) = X0 := superpose eq10 eq9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X5)) = X0 := superpose eq13 eq12
  have eq16 (X0 X1 X5 : G) : (X1 ◇ X5) = X0 := superpose eq13 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation10501_implies_Equation2 (G : Type*) [Magma G] (h : Equation10501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X3 ◇ X2) ◇ X2)) = (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X1)) ◇ ((X3 ◇ X4) ◇ X4)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq9 eq9
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq7 eq9
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = X1 := superpose eq29 eq27
  have eq42 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X2 ◇ X1) ◇ X1))) = X1 := superpose eq9 eq11
  have eq46 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = ((((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq9 eq11
  have eq145 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq7 eq41
  have eq148 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq41
  have eq152 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))))) := superpose eq41 eq11
  have eq169 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq148 eq11
  have eq197 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq169
  have eq198 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq9 eq169
  have eq221 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq145 eq41
  have eq238 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq221 eq152
  have eq246 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq221 eq197
  have eq252 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq169 eq246
  have eq270 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq252 eq238
  have eq286 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq252 eq145
  have eq303 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1))) = X1 := superpose eq286 eq42
  have eq329 (X0 X1 X2 : G) : ((X0 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) = X1 := superpose eq252 eq303
  have eq330 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X2 := superpose eq329 eq198
  have eq331 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq330 eq7
  have eq358 (X0 X1 X2 X3 : G) : ((((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (((X3 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) = X3 := superpose eq330 eq46
  have eq468 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X3 ◇ X1)) = X3 := superpose eq330 eq358
  have eq469 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq468 eq270
  have eq470 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq469 eq331
  have eq492 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq469 eq470
  have eq493 (X0 X3 : G) : X0 = X3 := superpose eq492 eq492
  have eq495 (X0 : G) : sK0 ≠ X0 := superpose eq493 eq8
  subsumption eq495 eq493


@[equational_result]
theorem Equation10503_implies_Equation2 (G : Type*) [Magma G] (h : Equation10503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10506_implies_Equation2 (G : Type*) [Magma G] (h : Equation10506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X4) ◇ ((X3 ◇ X0) ◇ ((X3 ◇ X3) ◇ X3)))) = X4 := superpose eq7 eq12
  have eq26 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq13
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq7 eq26
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq114 eq68


@[equational_result]
theorem Equation10507_implies_Equation2 (G : Type*) [Magma G] (h : Equation10507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10509_implies_Equation2 (G : Type*) [Magma G] (h : Equation10509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq44 eq32


@[equational_result]
theorem Equation10510_implies_Equation2 (G : Type*) [Magma G] (h : Equation10510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq10
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq155 eq42


@[equational_result]
theorem Equation10511_implies_Equation2 (G : Type*) [Magma G] (h : Equation10511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ ((X4 ◇ X0) ◇ ((X4 ◇ X5) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10512_implies_Equation2 (G : Type*) [Magma G] (h : Equation10512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10514_implies_Equation2 (G : Type*) [Magma G] (h : Equation10514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X5 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ X2))) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ ((X5 ◇ X4) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ X0) = X0 := superpose eq12 eq12
  have eq16 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq12
  have eq19 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X0) ◇ X1))) = X0 := superpose eq12 eq7
  have eq27 (X0 X1 X2 X3 X6 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) ◇ ((X6 ◇ X0) ◇ X2)) = X0 := superpose eq12 eq11
  have eq40 (X0 X1 X3 X6 X7 : G) : ((X6 ◇ X0) ◇ X3) = (X1 ◇ (X0 ◇ ((X7 ◇ ((X6 ◇ X0) ◇ X3)) ◇ X1))) := superpose eq11 eq7
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq11 eq14
  have eq48 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq11 eq14
  have eq61 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq16
  have eq82 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) = (X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4))) := superpose eq12 eq9
  have eq105 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) := superpose eq40 eq82
  have eq114 (X0 X2 X3 X6 : G) : (((X3 ◇ X2) ◇ X0) ◇ ((X6 ◇ X0) ◇ X2)) = X0 := superpose eq105 eq27
  have eq129 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq114 eq46
  have eq130 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq129 eq19
  have eq136 (X0 X1 X7 : G) : (X1 ◇ (X0 ◇ ((X7 ◇ X0) ◇ X1))) = X0 := superpose eq129 eq40
  have eq151 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq61 eq130
  have eq165 (X0 X1 X7 : G) : (X1 ◇ ((X7 ◇ X0) ◇ X1)) = X0 := superpose eq151 eq136
  have eq166 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq151 eq165
  have eq280 (X0 X2 : G) : X0 = X2 := superpose eq166 eq166
  have eq288 (X0 : G) : sK0 ≠ X0 := superpose eq280 eq8
  subsumption eq288 eq280


@[equational_result]
theorem Equation10515_implies_Equation2 (G : Type*) [Magma G] (h : Equation10515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X2))) = X0 := superpose eq12 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ ((X3 ◇ X0) ◇ X2)) = X0 := superpose eq12 eq15
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation10516_implies_Equation2 (G : Type*) [Magma G] (h : Equation10516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ X4)) = (X1 ◇ (X0 ◇ ((X5 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ X4))) ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ X4)) = (X1 ◇ (X0 ◇ (X0 ◇ X5))) := superpose eq7 eq9
  have eq15 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X5))) = X0 := superpose eq11 eq13
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X5)) = X0 := superpose eq16 eq15
  have eq19 (X0 X1 X5 : G) : (X1 ◇ X5) = X0 := superpose eq16 eq17
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation10517_implies_Equation2 (G : Type*) [Magma G] (h : Equation10517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 X6 X7 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ X5)) = (X1 ◇ (X0 ◇ ((X6 ◇ ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ X5))) ◇ X7))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 X7 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ X0) ◇ X5)) = (X1 ◇ (X0 ◇ (X0 ◇ X7))) := superpose eq7 eq9
  have eq15 (X0 X1 X7 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X7))) = X0 := superpose eq11 eq13
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X7 : G) : (X1 ◇ (X0 ◇ X7)) = X0 := superpose eq16 eq15
  have eq19 (X0 X1 X7 : G) : (X1 ◇ X7) = X0 := superpose eq16 eq17
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation10519_implies_Equation2 (G : Type*) [Magma G] (h : Equation10519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ X2) ◇ X2)) = (X1 ◇ (X0 ◇ ((X5 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = (X4 ◇ (X2 ◇ ((X5 ◇ X4) ◇ X4))) := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := superpose eq7 eq9
  have eq64 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq7
  have eq73 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) = X0 := superpose eq64 eq7
  have eq74 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ X1) ◇ X1))) = ((X3 ◇ X0) ◇ (X4 ◇ X2)) := superpose eq64 eq9
  have eq80 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = (X4 ◇ (X2 ◇ (X5 ◇ X4))) := superpose eq64 eq20
  have eq85 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) = X0 := superpose eq64 eq29
  have eq99 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ (X4 ◇ X2)) = (X1 ◇ (X0 ◇ (X5 ◇ X1))) := superpose eq64 eq74
  have eq107 (X2 X4 X5 : G) : (X4 ◇ (X2 ◇ (X5 ◇ X4))) = X2 := superpose eq85 eq80
  have eq111 (X0 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ (X4 ◇ X2)) = X0 := superpose eq107 eq99
  have eq114 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq111 eq73
  have eq116 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X4)) = X0 := superpose eq114 eq85
  have eq121 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X4) = X0 := superpose eq114 eq116
  have eq122 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq114 eq121
  have eq133 (X0 X1 : G) : X0 = X1 := superpose eq114 eq122
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq133 eq8
  subsumption eq146 eq133


@[equational_result]
theorem Equation10520_implies_Equation2 (G : Type*) [Magma G] (h : Equation10520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ ((X4 ◇ X2) ◇ X3)) = (X1 ◇ (X0 ◇ ((X5 ◇ X1) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) ◇ ((X4 ◇ X5) ◇ (X0 ◇ X4))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X6 ◇ (((X2 ◇ X0) ◇ ((X3 ◇ X1) ◇ X2)) ◇ ((X7 ◇ X6) ◇ X5))) = (X0 ◇ ((X4 ◇ X5) ◇ X1)) := superpose eq7 eq9
  have eq66 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ X5))) = X5 := superpose eq9 eq10
  have eq79 (X0 X1 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X1)) = X5 := superpose eq66 eq12
  have eq116 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq79 eq7
  have eq138 (X0 X2 : G) : X0 = X2 := superpose eq116 eq116
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq138 eq8
  subsumption eq140 eq138


@[equational_result]
theorem Equation10521_implies_Equation2 (G : Type*) [Magma G] (h : Equation10521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


