import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation25640_implies_Equation2 (G : Type*) [Magma G] (h : Equation25640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25641_implies_Equation2 (G : Type*) [Magma G] (h : Equation25641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25642_implies_Equation2 (G : Type*) [Magma G] (h : Equation25642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25644_implies_Equation2 (G : Type*) [Magma G] (h : Equation25644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25645_implies_Equation2 (G : Type*) [Magma G] (h : Equation25645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25646_implies_Equation2 (G : Type*) [Magma G] (h : Equation25646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25647_implies_Equation2 (G : Type*) [Magma G] (h : Equation25647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25649_implies_Equation2 (G : Type*) [Magma G] (h : Equation25649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25650_implies_Equation2 (G : Type*) [Magma G] (h : Equation25650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25651_implies_Equation2 (G : Type*) [Magma G] (h : Equation25651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25652_implies_Equation2 (G : Type*) [Magma G] (h : Equation25652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25653_implies_Equation2 (G : Type*) [Magma G] (h : Equation25653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25655_implies_Equation2 (G : Type*) [Magma G] (h : Equation25655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X5 ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) = (X1 ◇ ((X4 ◇ X5) ◇ X4)) := superpose eq9 eq9
  have eq28 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq10
  have eq29 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq10 eq10
  have eq35 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3)))) ◇ ((X5 ◇ X6) ◇ X5)) ◇ X0) = X2 := superpose eq10 eq9
  have eq42 (X0 X1 X2 X5 X6 : G) : (((X1 ◇ X2) ◇ ((X5 ◇ X6) ◇ X5)) ◇ X0) = X2 := superpose eq29 eq35
  have eq43 (X1 X4 X5 : G) : (X1 ◇ ((X4 ◇ X5) ◇ X4)) = X1 := superpose eq42 eq17
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq43 eq42
  have eq51 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X0)) = X3 := superpose eq45 eq28
  have eq55 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq51 eq29
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq55 eq55
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq70 eq58


@[equational_result]
theorem Equation25656_implies_Equation2 (G : Type*) [Magma G] (h : Equation25656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq12 eq15
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq57 eq24


@[equational_result]
theorem Equation25657_implies_Equation2 (G : Type*) [Magma G] (h : Equation25657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq10 eq16
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation25658_implies_Equation2 (G : Type*) [Magma G] (h : Equation25658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25660_implies_Equation2 (G : Type*) [Magma G] (h : Equation25660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25661_implies_Equation2 (G : Type*) [Magma G] (h : Equation25661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25662_implies_Equation2 (G : Type*) [Magma G] (h : Equation25662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25663_implies_Equation2 (G : Type*) [Magma G] (h : Equation25663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25665_implies_Equation2 (G : Type*) [Magma G] (h : Equation25665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25666_implies_Equation2 (G : Type*) [Magma G] (h : Equation25666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25667_implies_Equation2 (G : Type*) [Magma G] (h : Equation25667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25668_implies_Equation2 (G : Type*) [Magma G] (h : Equation25668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25670_implies_Equation2 (G : Type*) [Magma G] (h : Equation25670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25671_implies_Equation2 (G : Type*) [Magma G] (h : Equation25671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25672_implies_Equation2 (G : Type*) [Magma G] (h : Equation25672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25673_implies_Equation2 (G : Type*) [Magma G] (h : Equation25673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25675_implies_Equation2 (G : Type*) [Magma G] (h : Equation25675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25676_implies_Equation2 (G : Type*) [Magma G] (h : Equation25676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25677_implies_Equation2 (G : Type*) [Magma G] (h : Equation25677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25678_implies_Equation2 (G : Type*) [Magma G] (h : Equation25678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25679_implies_Equation2 (G : Type*) [Magma G] (h : Equation25679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25681_implies_Equation2 (G : Type*) [Magma G] (h : Equation25681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq10 eq10
  have eq21 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X4 := superpose eq14 eq11
  have eq26 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq21 eq14
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq10 eq26
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq45 eq31


@[equational_result]
theorem Equation25682_implies_Equation2 (G : Type*) [Magma G] (h : Equation25682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq10 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X3))) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq17 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X3))) = X1 := superpose eq13 eq12
  have eq19 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X0)) = X4 := superpose eq17 eq9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq10 eq19
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X3 ◇ X2) := superpose eq19 eq19
  have eq28 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq25 eq26
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq28 eq25
  have eq35 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq28 eq29
  have eq37 (X0 X1 : G) : X0 = X1 := superpose eq28 eq35
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq39 eq37


@[equational_result]
theorem Equation25683_implies_Equation2 (G : Type*) [Magma G] (h : Equation25683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq10 eq15
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq59 eq26


@[equational_result]
theorem Equation25684_implies_Equation2 (G : Type*) [Magma G] (h : Equation25684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25686_implies_Equation2 (G : Type*) [Magma G] (h : Equation25686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25687_implies_Equation2 (G : Type*) [Magma G] (h : Equation25687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25688_implies_Equation2 (G : Type*) [Magma G] (h : Equation25688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25689_implies_Equation2 (G : Type*) [Magma G] (h : Equation25689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25691_implies_Equation2 (G : Type*) [Magma G] (h : Equation25691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25692_implies_Equation2 (G : Type*) [Magma G] (h : Equation25692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25693_implies_Equation2 (G : Type*) [Magma G] (h : Equation25693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25694_implies_Equation2 (G : Type*) [Magma G] (h : Equation25694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25696_implies_Equation2 (G : Type*) [Magma G] (h : Equation25696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25697_implies_Equation2 (G : Type*) [Magma G] (h : Equation25697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25698_implies_Equation2 (G : Type*) [Magma G] (h : Equation25698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25699_implies_Equation2 (G : Type*) [Magma G] (h : Equation25699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25701_implies_Equation2 (G : Type*) [Magma G] (h : Equation25701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25702_implies_Equation2 (G : Type*) [Magma G] (h : Equation25702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25703_implies_Equation2 (G : Type*) [Magma G] (h : Equation25703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25704_implies_Equation2 (G : Type*) [Magma G] (h : Equation25704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25705_implies_Equation2 (G : Type*) [Magma G] (h : Equation25705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25707_implies_Equation2 (G : Type*) [Magma G] (h : Equation25707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 : G) : ((X1 ◇ X0) ◇ (X6 ◇ X1)) = X6 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X6 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))))) = X6 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq10 eq10
  have eq22 (X0 X3 X6 : G) : (X0 ◇ (X6 ◇ X3)) = X6 := superpose eq14 eq11
  have eq26 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq22 eq14
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq10 eq26
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq70 eq32


@[equational_result]
theorem Equation25708_implies_Equation2 (G : Type*) [Magma G] (h : Equation25708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X0) ◇ (X6 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5))))) = X6 := superpose eq7 eq7
  have eq11 (X0 X6 : G) : (X0 ◇ (X6 ◇ X0)) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X4))) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq19 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X4))) = X1 := superpose eq14 eq13
  have eq21 (X0 X1 X3 X6 : G) : ((X1 ◇ X0) ◇ (X6 ◇ X3)) = X6 := superpose eq19 eq10
  have eq25 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq11 eq21
  have eq30 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq25 eq19
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq11 eq30
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq57 eq32


@[equational_result]
theorem Equation25709_implies_Equation2 (G : Type*) [Magma G] (h : Equation25709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X6 : G) : (X0 ◇ (X6 ◇ X3)) = X6 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25710_implies_Equation2 (G : Type*) [Magma G] (h : Equation25710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X6 ◇ X5)) = X6 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25711_implies_Equation2 (G : Type*) [Magma G] (h : Equation25711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X0 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X7 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25713_implies_Equation2 (G : Type*) [Magma G] (h : Equation25713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25714_implies_Equation2 (G : Type*) [Magma G] (h : Equation25714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25715_implies_Equation2 (G : Type*) [Magma G] (h : Equation25715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25716_implies_Equation2 (G : Type*) [Magma G] (h : Equation25716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25717_implies_Equation2 (G : Type*) [Magma G] (h : Equation25717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X1 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25719_implies_Equation2 (G : Type*) [Magma G] (h : Equation25719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25720_implies_Equation2 (G : Type*) [Magma G] (h : Equation25720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25721_implies_Equation2 (G : Type*) [Magma G] (h : Equation25721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25722_implies_Equation2 (G : Type*) [Magma G] (h : Equation25722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25723_implies_Equation2 (G : Type*) [Magma G] (h : Equation25723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X2 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25725_implies_Equation2 (G : Type*) [Magma G] (h : Equation25725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25726_implies_Equation2 (G : Type*) [Magma G] (h : Equation25726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25727_implies_Equation2 (G : Type*) [Magma G] (h : Equation25727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25728_implies_Equation2 (G : Type*) [Magma G] (h : Equation25728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25729_implies_Equation2 (G : Type*) [Magma G] (h : Equation25729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X3 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25731_implies_Equation2 (G : Type*) [Magma G] (h : Equation25731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25732_implies_Equation2 (G : Type*) [Magma G] (h : Equation25732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25733_implies_Equation2 (G : Type*) [Magma G] (h : Equation25733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25734_implies_Equation2 (G : Type*) [Magma G] (h : Equation25734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25735_implies_Equation2 (G : Type*) [Magma G] (h : Equation25735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25737_implies_Equation2 (G : Type*) [Magma G] (h : Equation25737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X5 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25738_implies_Equation2 (G : Type*) [Magma G] (h : Equation25738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X5 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25739_implies_Equation2 (G : Type*) [Magma G] (h : Equation25739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X5 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25740_implies_Equation2 (G : Type*) [Magma G] (h : Equation25740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X5 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25741_implies_Equation2 (G : Type*) [Magma G] (h : Equation25741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X5 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25742_implies_Equation2 (G : Type*) [Magma G] (h : Equation25742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X5 ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25951_implies_Equation2 (G : Type*) [Magma G] (h : Equation25951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq7 eq14
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq96 eq27


@[equational_result]
theorem Equation25953_implies_Equation2 (G : Type*) [Magma G] (h : Equation25953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq10 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq38 eq28


@[equational_result]
theorem Equation25954_implies_Equation2 (G : Type*) [Magma G] (h : Equation25954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq43 eq21


@[equational_result]
theorem Equation25955_implies_Equation2 (G : Type*) [Magma G] (h : Equation25955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation25961_implies_Equation2 (G : Type*) [Magma G] (h : Equation25961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq47 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq60 (X0 X2 : G) : X0 = X2 := superpose eq7 eq47
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq122 eq60


@[equational_result]
theorem Equation25963_implies_Equation2 (G : Type*) [Magma G] (h : Equation25963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq9 eq9
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq41 eq17


@[equational_result]
theorem Equation25965_implies_Equation2 (G : Type*) [Magma G] (h : Equation25965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation25971_implies_Equation2 (G : Type*) [Magma G] (h : Equation25971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) = X0 := superpose eq7 eq10
  have eq39 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq25 eq12
  have eq41 (X0 X2 : G) : X0 = X2 := superpose eq7 eq39
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq66 eq41


@[equational_result]
theorem Equation25972_implies_Equation2 (G : Type*) [Magma G] (h : Equation25972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq10
  have eq15 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq10
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq7 eq9
  have eq32 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X3 ◇ X3) ◇ (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)))) ◇ ((X0 ◇ X0) ◇ X1)) = X3 := superpose eq9 eq7
  have eq38 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ X1))) := superpose eq14 eq9
  have eq89 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq25 eq7
  have eq111 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq89 eq15
  have eq112 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose eq89 eq38
  have eq159 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X3 ◇ X3) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ (X0 ◇ X1)) = X3 := superpose eq111 eq32
  have eq242 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ (X0 ◇ X1)) = X3 := superpose eq111 eq159
  have eq260 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq111 eq112
  have eq261 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq111 eq260
  have eq262 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq111 eq261
  have eq274 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) = X3 := superpose eq262 eq242
  have eq328 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X0))) ◇ X0) = X3 := superpose eq262 eq274
  have eq329 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = X3 := superpose eq262 eq328
  have eq330 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq262 eq329
  have eq331 (X0 X1 : G) : X0 = X1 := superpose eq111 eq330
  have eq339 (X0 : G) : sK0 ≠ X0 := superpose eq331 eq8
  subsumption eq339 eq331


@[equational_result]
theorem Equation25973_implies_Equation2 (G : Type*) [Magma G] (h : Equation25973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X4)) = X1 := superpose eq7 eq7
  have eq52 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq7 eq52
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq191 eq68


@[equational_result]
theorem Equation25976_implies_Equation2 (G : Type*) [Magma G] (h : Equation25976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X2 := superpose eq10 eq9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq11 eq7
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq30 eq22


@[equational_result]
theorem Equation25977_implies_Equation2 (G : Type*) [Magma G] (h : Equation25977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq72 eq16


@[equational_result]
theorem Equation25979_implies_Equation2 (G : Type*) [Magma G] (h : Equation25979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) = X3 := superpose eq7 eq7
  have eq58 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq76 eq58


@[equational_result]
theorem Equation25980_implies_Equation2 (G : Type*) [Magma G] (h : Equation25980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation25981_implies_Equation2 (G : Type*) [Magma G] (h : Equation25981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation25982_implies_Equation2 (G : Type*) [Magma G] (h : Equation25982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation25985_implies_Equation2 (G : Type*) [Magma G] (h : Equation25985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0)))) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X0)) = ((X1 ◇ (((X2 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq11 eq11
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) = ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X0) ◇ ((X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X3)) := superpose eq7 eq9
  have eq51 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) := superpose eq7 eq9
  have eq55 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))) = ((((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X3) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))) ◇ X4)) := superpose eq10 eq9
  have eq72 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq51 eq19
  have eq80 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X0) ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X3)) := superpose eq72 eq48
  have eq91 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X2)) := superpose eq7 eq51
  have eq92 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ X0) := superpose eq7 eq51
  have eq108 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq92 eq7
  have eq109 (X0 X1 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq92 eq9
  have eq111 (X0 X1 : G) : (X0 ◇ X0) = ((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) ◇ X0) := superpose eq92 eq14
  have eq131 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3)) := superpose eq92 eq80
  have eq146 (X0 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq108 eq131
  have eq197 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) := superpose eq10 eq92
  have eq198 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq108 eq92
  have eq201 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq92 eq92
  have eq203 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq92 eq108
  have eq204 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq92 eq109
  have eq205 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq92 eq109
  have eq208 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq108 eq198
  have eq229 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := superpose eq208 eq205
  have eq231 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq229 eq204
  have eq232 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq229 eq208
  have eq235 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq203 eq231
  have eq248 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = ((((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq146 eq10
  have eq250 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X0))) := superpose eq146 eq92
  have eq261 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq235 eq248
  have eq270 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq261 eq250
  have eq271 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq92 eq270
  have eq272 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq201 eq271
  have eq273 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq232 eq272
  have eq275 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))) := superpose eq273 eq197
  have eq280 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq273 eq108
  have eq281 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq273 eq111
  have eq304 (X0 X1 X3 X4 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = ((((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X3) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X4)) := superpose eq275 eq55
  have eq307 (X0 X1 X3 X4 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = ((((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X3) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X4)) := superpose eq273 eq304
  have eq311 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) := superpose eq280 eq91
  have eq312 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq280 eq275
  have eq317 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X3) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X4)) := superpose eq280 eq307
  have eq324 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq273 eq311
  have eq325 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq273 eq324
  have eq326 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq273 eq312
  have eq327 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq325 eq326
  have eq328 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X0 := superpose eq273 eq327
  have eq337 (X0 X3 X4 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq273 eq317
  have eq338 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X0) ◇ (X0 ◇ X4)) = X0 := superpose eq273 eq337
  have eq339 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq328 eq281
  have eq340 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq339 eq338
  have eq346 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq339 eq340
  have eq349 (X0 X1 : G) : X0 = X1 := superpose eq339 eq346
  have eq351 (X0 : G) : sK0 ≠ X0 := superpose eq349 eq8
  subsumption eq351 eq349


@[equational_result]
theorem Equation25988_implies_Equation2 (G : Type*) [Magma G] (h : Equation25988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) := superpose eq7 eq9
  have eq43 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ X0) := superpose eq7 eq22
  have eq57 (X0 X1 X2 : G) : ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) ◇ X2) = X1 := superpose eq22 eq10
  have eq105 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq43 eq22
  have eq145 (X0 X1 X2 : G) : ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) = X1 := superpose eq105 eq57
  have eq162 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = X1 := superpose eq105 eq145
  have eq282 (X0 X3 : G) : X0 = X3 := superpose eq162 eq162
  have eq470 (X0 : G) : sK0 ≠ X0 := superpose eq282 eq8
  subsumption eq470 eq282


@[equational_result]
theorem Equation25990_implies_Equation2 (G : Type*) [Magma G] (h : Equation25990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq10 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq40 eq30


@[equational_result]
theorem Equation25992_implies_Equation2 (G : Type*) [Magma G] (h : Equation25992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation25995_implies_Equation2 (G : Type*) [Magma G] (h : Equation25995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = ((X1 ◇ (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2)) = ((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2)) := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq20 eq14
  have eq43 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ X0) := superpose eq7 eq13
  have eq82 (X0 X1 X2 : G) : ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq20 eq7
  have eq92 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2)) = X1 := superpose eq82 eq31
  have eq103 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq43
  have eq136 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq82 eq103
  have eq214 (X0 X1 X2 X3 : G) : (X1 ◇ ((((((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ (X0 ◇ (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ X3))) ◇ X1) ◇ X1)) = X3 := superpose eq92 eq92
  have eq228 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq92 eq7
  have eq239 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = X1 := superpose eq228 eq92
  have eq242 (X0 X1 X3 : G) : (X1 ◇ ((((X0 ◇ X3) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X1) ◇ X1)) = X3 := superpose eq228 eq214
  have eq250 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X2 := superpose eq239 eq228
  have eq263 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X0 ◇ X3)))) = X3 := superpose eq250 eq242
  have eq264 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq136 eq263
  have eq265 (X0 X3 : G) : X0 = X3 := superpose eq264 eq264
  have eq276 (X0 : G) : sK0 ≠ X0 := superpose eq265 eq8
  subsumption eq276 eq265


@[equational_result]
theorem Equation25998_implies_Equation2 (G : Type*) [Magma G] (h : Equation25998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1)) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1)) = X0 := superpose eq7 eq9
  have eq44 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) = X2 := superpose eq19 eq19
  have eq62 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq44 eq11
  have eq66 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq62 eq9
  have eq72 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq66 eq7
  have eq88 (X0 X3 : G) : X0 = X3 := superpose eq72 eq72
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq90 eq88


@[equational_result]
theorem Equation26000_implies_Equation2 (G : Type*) [Magma G] (h : Equation26000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq27 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq11 eq11
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq7 eq27
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq107 eq35


@[equational_result]
theorem Equation26001_implies_Equation2 (G : Type*) [Magma G] (h : Equation26001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (((X3 ◇ X3) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4)) := superpose eq7 eq9
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X4) ◇ (((X3 ◇ X3) ◇ (X1 ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4))) ◇ (X5 ◇ X5)) = ((X2 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X2))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) = (((X4 ◇ X4) ◇ (X1 ◇ (X4 ◇ X4))) ◇ (X5 ◇ X5)) := superpose eq9 eq9
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X1)) = (((X3 ◇ X3) ◇ X0) ◇ (X4 ◇ X4)) := superpose eq7 eq9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq9
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X1) ◇ X1)) = X0 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X3) ◇ X3) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X3))) ◇ (X4 ◇ X4)) = X3 := superpose eq9 eq7
  have eq25 (X0 X1 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (((X3 ◇ X3) ◇ X0) ◇ (X4 ◇ X4)) := superpose eq7 eq10
  have eq26 (X1 X2 X3 X4 X5 : G) : (((X4 ◇ X4) ◇ (((X3 ◇ X3) ◇ (X1 ◇ (X3 ◇ X3))) ◇ (X4 ◇ X4))) ◇ (X5 ◇ X5)) = ((X2 ◇ X2) ◇ X1) := superpose eq7 eq11
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ (X2 ◇ X2))) := superpose eq9 eq19
  have eq35 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) = X1 := superpose eq9 eq19
  have eq37 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X3 ◇ X3)) := superpose eq19 eq7
  have eq41 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X1 ◇ X1)) := superpose eq7 eq31
  have eq159 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq37 eq41
  have eq164 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) := superpose eq41 eq19
  have eq198 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X4) ◇ ((X3 ◇ X3) ◇ X1)) ◇ (X5 ◇ X5)) = ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq25 eq25
  have eq375 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ X2)) = (X3 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq159 eq18
  have eq441 (X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X2) ◇ X2)) = (X3 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq41 eq375
  have eq838 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ X2)) ◇ (X3 ◇ X3)) = X2 := superpose eq164 eq7
  have eq2439 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X1 ◇ (X4 ◇ X4)) ◇ X3) ◇ X3)) = ((X1 ◇ (X4 ◇ X4)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2))) := superpose eq25 eq441
  have eq2593 (X0 X1 X2 X4 : G) : ((X1 ◇ (X4 ◇ X4)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2))) = X1 := superpose eq19 eq2439
  have eq2667 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X7 ◇ X7) ◇ ((X5 ◇ X5) ◇ (X1 ◇ (X5 ◇ X5)))) = (((X3 ◇ X3) ◇ (((X4 ◇ X4) ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) ◇ (X6 ◇ X6)) := superpose eq14 eq26
  have eq4796 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X4 ◇ X4) = (((((X0 ◇ X0) ◇ X1) ◇ (X4 ◇ X4)) ◇ ((((X5 ◇ X5) ◇ (((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ (X1 ◇ (X3 ◇ X3))) ◇ (X2 ◇ X2))) ◇ (X5 ◇ X5))) ◇ (X6 ◇ X6)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X4 ◇ X4)))) ◇ (X7 ◇ X7)) := superpose eq26 eq21
  have eq4850 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) = (((((X0 ◇ (X1 ◇ X1)) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) ◇ X0) ◇ (X4 ◇ X4)) := superpose eq19 eq21
  have eq5052 (X0 X1 X4 : G) : (((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) ◇ (X4 ◇ X4)) = X0 := superpose eq35 eq4850
  have eq5169 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ (X2 ◇ X2)) ◇ X0) ◇ X0) ◇ X0) := superpose eq5052 eq19
  have eq14773 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)))) = X0 := superpose eq2593 eq19
  have eq24928 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X0) ◇ X0) = (((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) ◇ (X3 ◇ X3)) := superpose eq5169 eq838
  have eq25131 (X0 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq5052 eq24928
  have eq26034 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X3) ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X4 ◇ X4)) = (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1)) := superpose eq25131 eq15
  have eq26355 (X0 X2 X3 X4 : G) : (((X3 ◇ X3) ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X4 ◇ X4)) = X0 := superpose eq19 eq26034
  have eq26360 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq26355 eq198
  have eq26374 (X0 X1 X2 X3 X4 X6 : G) : (((X3 ◇ X3) ◇ (((X4 ◇ X4) ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) ◇ (X6 ◇ X6)) = X1 := superpose eq26360 eq2667
  have eq26389 (X0 X1 X4 X7 : G) : (X4 ◇ X4) = (((((X0 ◇ X0) ◇ X1) ◇ (X4 ◇ X4)) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X4 ◇ X4)))) ◇ (X7 ◇ X7)) := superpose eq26374 eq4796
  have eq26392 (X1 X4 X7 : G) : (X4 ◇ X4) = (X1 ◇ (X7 ◇ X7)) := superpose eq14773 eq26389
  have eq26602 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq26392
  have eq27629 (X0 X2 : G) : X0 = X2 := superpose eq26602 eq26602
  have eq27642 (X0 : G) : sK0 ≠ X0 := superpose eq27629 eq8
  subsumption eq27642 eq27629


@[equational_result]
theorem Equation26002_implies_Equation2 (G : Type*) [Magma G] (h : Equation26002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26004_implies_Equation2 (G : Type*) [Magma G] (h : Equation26004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq7 eq10
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq10 eq10
  have eq34 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq7
  have eq94 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq7 eq34
  have eq114 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq94 eq94
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq94 eq10
  have eq137 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq123 eq29
  have eq150 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq137 eq137
  have eq156 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) := superpose eq137 eq10
  have eq157 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) := superpose eq137 eq30
  have eq160 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq137 eq9
  have eq169 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq114 eq150
  have eq170 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = X0 := superpose eq169 eq156
  have eq173 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq170 eq157
  have eq179 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq173 eq160
  have eq180 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq169 eq179
  have eq280 (X0 X2 : G) : X0 = X2 := superpose eq180 eq180
  have eq288 (X0 : G) : sK0 ≠ X0 := superpose eq280 eq8
  subsumption eq288 eq280


@[equational_result]
theorem Equation26006_implies_Equation2 (G : Type*) [Magma G] (h : Equation26006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X1 ◇ X4)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq16 eq16
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq45 eq45
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq79 eq50


@[equational_result]
theorem Equation26008_implies_Equation2 (G : Type*) [Magma G] (h : Equation26008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2)) = X0 := superpose eq7 eq9
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X3) = ((((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X4) ◇ X0) ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X4) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X4))) := superpose eq9 eq10
  have eq44 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq9 eq10
  have eq55 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0))) := superpose eq13 eq44
  have eq56 (X1 X3 : G) : (X1 ◇ X1) = (X1 ◇ X3) := superpose eq7 eq55
  have eq58 (X0 X1 X3 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq56 eq9
  have eq76 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ X3) = ((((X0 ◇ X0) ◇ X4) ◇ X0) ◇ (((X0 ◇ X0) ◇ X4) ◇ ((X0 ◇ X0) ◇ X4))) := superpose eq58 eq37
  have eq81 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq10 eq76
  have eq82 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X2)) = X0 := superpose eq81 eq35
  have eq89 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq81 eq82
  have eq115 (X0 X2 : G) : X0 = X2 := superpose eq89 eq89
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq115 eq8
  subsumption eq127 eq115


@[equational_result]
theorem Equation26010_implies_Equation2 (G : Type*) [Magma G] (h : Equation26010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X3)) = (((X1 ◇ X2) ◇ (X0 ◇ X4)) ◇ ((X1 ◇ X2) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ X4)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X4)) := superpose eq7 eq10
  have eq49 (X0 X1 X2 X3 X4 X6 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X4)) ◇ (X0 ◇ X6)) = X2 := superpose eq9 eq7
  have eq53 (X0 X1 X2 X3 X4 X5 X7 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X5)) ◇ X0) ◇ (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X5)) ◇ X7)) = X1 := superpose eq9 eq10
  have eq78 (X0 X1 X2 X3 X4 X6 X7 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X4)) ◇ X6) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X4)) ◇ (X0 ◇ X7)) := superpose eq9 eq14
  have eq123 (X0 X1 X2 X3 X4 X6 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X4)) ◇ X6) = X2 := superpose eq49 eq78
  have eq124 (X0 X1 X2 X3 X4 X5 X7 : G) : (X3 ◇ (((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X5)) ◇ X7)) = X1 := superpose eq123 eq53
  have eq127 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq123 eq124
  have eq156 (X0 X3 : G) : X0 = X3 := superpose eq7 eq127
  have eq204 (X0 : G) : sK0 ≠ X0 := superpose eq156 eq8
  subsumption eq204 eq156


@[equational_result]
theorem Equation26014_implies_Equation2 (G : Type*) [Magma G] (h : Equation26014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) = X1 := superpose eq10 eq10
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq16 eq14
  have eq31 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = X0 := superpose eq27 eq7
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq31 eq31
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation26016_implies_Equation2 (G : Type*) [Magma G] (h : Equation26016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) = X3 := superpose eq7 eq7
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq63 eq25


@[equational_result]
theorem Equation26017_implies_Equation2 (G : Type*) [Magma G] (h : Equation26017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation26018_implies_Equation2 (G : Type*) [Magma G] (h : Equation26018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq47 eq14


@[equational_result]
theorem Equation26019_implies_Equation2 (G : Type*) [Magma G] (h : Equation26019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26021_implies_Equation2 (G : Type*) [Magma G] (h : Equation26021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X0)) = (((X0 ◇ X1) ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X0)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X3) ◇ X0)))) := superpose eq7 eq10
  have eq15 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X3) ◇ X0)))) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq10 eq7
  have eq53 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = ((((X0 ◇ X2) ◇ X1) ◇ (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X4) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2))))) ◇ (X0 ◇ X2)) := superpose eq10 eq11
  have eq75 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq17
  have eq85 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq13 eq17
  have eq1161 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1))) ◇ X1)) ◇ (X1 ◇ X3)) = X1 := superpose eq53 eq75
  have eq1206 (X0 X1 X2 X3 : G) : ((X3 ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq85 eq1161
  have eq1297 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq1206
  have eq1410 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) = X0 := superpose eq7 eq1297
  have eq1413 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq1297 eq1297
  have eq1573 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq1413 eq13
  have eq1739 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq1573 eq7
  have eq1764 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq1573 eq14
  have eq1803 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq1573 eq1297
  have eq1814 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1573 eq1764
  have eq1815 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq1739 eq1803
  have eq1816 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1573 eq1815
  have eq1826 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1816 eq1814
  have eq1888 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq1826 eq1410
  have eq1891 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq1826 eq1888
  have eq1892 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq1891 eq1826
  have eq1897 (X0 X1 X3 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X3) ◇ X0)))) := superpose eq1892 eq14
  have eq1898 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq1892 eq15
  have eq2303 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq1892 eq1897
  have eq2304 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1892 eq1898
  have eq2305 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq1892 eq2304
  have eq2306 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1816 eq2305
  have eq2307 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq2306 eq2303
  have eq2367 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq2306 eq2307
  have eq2503 (X0 X1 : G) : X0 = X1 := superpose eq2306 eq2367
  have eq2505 (X0 : G) : sK0 ≠ X0 := superpose eq2503 eq8
  subsumption eq2505 eq2503


@[equational_result]
theorem Equation26022_implies_Equation2 (G : Type*) [Magma G] (h : Equation26022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X0)) = (X0 ◇ X0) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) := superpose eq10 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq13 eq15
  have eq39 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq10 eq16
  have eq70 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq39 eq20
  have eq74 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq70 eq16
  have eq80 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq70 eq74
  have eq81 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq70 eq80
  have eq121 (X0 X1 : G) : X0 = X1 := superpose eq81 eq70
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq121 eq8
  subsumption eq123 eq121


@[equational_result]
theorem Equation26023_implies_Equation2 (G : Type*) [Magma G] (h : Equation26023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq24 (X0 X1 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X4)) = X0 := superpose eq11 eq10
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ X0) := superpose eq11 eq10
  have eq46 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq27 eq27
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq11 eq27
  have eq79 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq48 eq46
  have eq94 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ (X0 ◇ X4)) = X0 := superpose eq79 eq24
  have eq106 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = X0 := superpose eq79 eq94
  have eq107 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq79 eq106
  have eq112 (X0 X1 : G) : X0 = X1 := superpose eq107 eq79
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq112 eq8
  subsumption eq122 eq112


@[equational_result]
theorem Equation26025_implies_Equation2 (G : Type*) [Magma G] (h : Equation26025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X0)) = ((X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X0)))) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X5 : G) : ((X5 ◇ (X1 ◇ X0)) ◇ (X5 ◇ X5)) = X0 := superpose eq10 eq9
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose eq10 eq20
  have eq78 (X0 X3 : G) : X0 = X3 := superpose eq7 eq29
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq168 eq78


@[equational_result]
theorem Equation26027_implies_Equation2 (G : Type*) [Magma G] (h : Equation26027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X0)) ◇ X4)) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq116 eq42


@[equational_result]
theorem Equation26030_implies_Equation2 (G : Type*) [Magma G] (h : Equation26030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X0)) = ((X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X0)))) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X1) = (X0 ◇ ((((X3 ◇ X3) ◇ X1) ◇ (X3 ◇ X3)) ◇ (((X3 ◇ X3) ◇ X1) ◇ (X3 ◇ X3)))) := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))))) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq31 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))) = (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ (X1 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq15 eq15
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X2 ◇ (X1 ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq10 eq15
  have eq47 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) := superpose eq15 eq10
  have eq49 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) = X2 := superpose eq15 eq7
  have eq57 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = ((X3 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq15 eq9
  have eq61 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ (X1 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ (X1 ◇ X1))))) := superpose eq15 eq10
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X2 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))))) := superpose eq7 eq11
  have eq68 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) = (X2 ◇ (((X0 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3)))) := superpose eq11 eq11
  have eq98 (X0 X2 X3 : G) : (X0 ◇ X0) = (X2 ◇ (((X0 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3)))) := superpose eq11 eq68
  have eq99 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq98 eq57
  have eq109 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq99 eq38
  have eq112 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq99 eq64
  have eq118 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ (X1 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ (X1 ◇ X1)))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))) := superpose eq112 eq31
  have eq121 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))))) := superpose eq118 eq61
  have eq122 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq47 eq121
  have eq124 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))))) := superpose eq122 eq13
  have eq129 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq122 eq109
  have eq145 (X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X1)) = X2 := superpose eq129 eq49
  have eq170 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq145 eq122
  have eq172 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq170 eq124
  have eq176 (X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = X2 := superpose eq170 eq145
  have eq183 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0)))) = X1 := superpose eq170 eq172
  have eq184 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq170 eq176
  have eq186 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) = X1 := superpose eq184 eq183
  have eq192 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq184 eq186
  have eq193 (X0 X3 : G) : X0 = X3 := superpose eq192 eq192
  have eq205 (X0 : G) : sK0 ≠ X0 := superpose eq193 eq8
  subsumption eq205 eq193


@[equational_result]
theorem Equation26031_implies_Equation2 (G : Type*) [Magma G] (h : Equation26031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq71 eq16


@[equational_result]
theorem Equation26033_implies_Equation2 (G : Type*) [Magma G] (h : Equation26033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq10 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq41 eq31


@[equational_result]
theorem Equation26034_implies_Equation2 (G : Type*) [Magma G] (h : Equation26034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation26035_implies_Equation2 (G : Type*) [Magma G] (h : Equation26035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq21 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq7 eq21
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq127 eq51


@[equational_result]
theorem Equation26036_implies_Equation2 (G : Type*) [Magma G] (h : Equation26036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation26038_implies_Equation2 (G : Type*) [Magma G] (h : Equation26038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (((X0 ◇ X1) ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X4) ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X1 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X4) ◇ X1)) ◇ (X0 ◇ X2))) := superpose eq7 eq9
  have eq26 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq9
  have eq52 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((((X2 ◇ X0) ◇ X2) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X2 ◇ X0) ◇ X2) ◇ X1))) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq10 eq11
  have eq65 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X3) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq10 eq11
  have eq110 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = (X2 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X2)) := superpose eq26 eq26
  have eq115 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ X0)) := superpose eq11 eq26
  have eq118 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq10 eq26
  have eq123 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3) ◇ X1)) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq26 eq26
  have eq127 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X0 ◇ ((X1 ◇ X3) ◇ X0)) := superpose eq26 eq26
  have eq131 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq26 eq7
  have eq159 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) = (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0))) := superpose eq26 eq9
  have eq164 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = X1 := superpose eq26 eq10
  have eq171 (X0 X1 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq118 eq65
  have eq175 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X4) ◇ X1)) := superpose eq7 eq127
  have eq176 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ X1)) := superpose eq10 eq127
  have eq184 (X0 X1 X2 X4 : G) : (X2 ◇ ((X1 ◇ X4) ◇ X2)) = (X2 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X2)) := superpose eq26 eq127
  have eq185 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1))) := superpose eq7 eq127
  have eq305 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X2) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) := superpose eq175 eq17
  have eq316 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq185 eq115
  have eq427 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) = (((X1 ◇ X3) ◇ X1) ◇ ((((X0 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) ◇ (X1 ◇ X3))) := superpose eq26 eq305
  have eq466 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((((X0 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq305 eq131
  have eq483 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X2 ◇ (X3 ◇ X2)) := superpose eq305 eq176
  have eq489 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq7 eq176
  have eq671 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq7 eq483
  have eq817 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq671 eq118
  have eq818 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq671 eq466
  have eq823 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3) ◇ X1)) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq671 eq123
  have eq847 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) = (X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) := superpose eq671 eq110
  have eq850 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq671 eq131
  have eq861 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0))) := superpose eq671 eq159
  have eq864 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = X1 := superpose eq671 eq164
  have eq868 (X0 X1 X2 X4 : G) : (X2 ◇ ((X1 ◇ X4) ◇ X2)) = (X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) := superpose eq671 eq184
  have eq885 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = (((X1 ◇ X3) ◇ X1) ◇ ((((X0 ◇ X2) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (X1 ◇ X3))) := superpose eq671 eq427
  have eq934 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((((X2 ◇ X0) ◇ X2) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq671 eq52
  have eq948 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq817 eq171
  have eq949 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq176 eq948
  have eq951 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ X1)) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq671 eq823
  have eq952 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq176 eq951
  have eq967 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) := superpose eq176 eq847
  have eq968 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ X1) ◇ X1) := superpose eq671 eq967
  have eq972 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0))) := superpose eq671 eq861
  have eq976 (X1 X2 X4 : G) : (X2 ◇ (X1 ◇ X2)) = (X2 ◇ ((X1 ◇ X4) ◇ X2)) := superpose eq176 eq868
  have eq1007 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq976 eq316
  have eq1036 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq976 eq864
  have eq1039 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq976 eq952
  have eq1057 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq976 eq949
  have eq1084 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq976 eq972
  have eq1130 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq1057 eq1036
  have eq1149 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq976 eq1084
  have eq1343 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2)))) = (((((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq934 eq934
  have eq1344 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X4 ◇ ((X0 ◇ X1) ◇ X0)))) = (((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq483 eq934
  have eq1403 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) = (((((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq489 eq1343
  have eq1404 (X0 X1 X4 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X4 ◇ ((X0 ◇ X1) ◇ X0)))) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq671 eq1344
  have eq1405 (X0 X1 X4 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X4 ◇ ((X0 ◇ X1) ◇ X0)))) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq968 eq1404
  have eq1406 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X0) = ((X4 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X4 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq671 eq1405
  have eq1407 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) := superpose eq1406 eq489
  have eq1415 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = (((((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq1407 eq1403
  have eq1422 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = (((((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq1407 eq1415
  have eq1423 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq1407 eq1422
  have eq1427 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq1423 eq818
  have eq1435 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) := superpose eq1427 eq1149
  have eq1441 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq1435 eq1007
  have eq1515 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq1435 eq1441
  have eq1524 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq1515 eq1130
  have eq1530 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq1524 eq1039
  have eq1533 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq1530 eq671
  have eq1672 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq1533 eq850
  have eq1677 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X3) ◇ X1) ◇ ((((X0 ◇ X2) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X3))) := superpose eq1533 eq885
  have eq1682 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) := superpose eq1533 eq1423
  have eq1692 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq1533 eq1672
  have eq1700 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X3) ◇ X1) ◇ ((((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X3))) := superpose eq1533 eq1677
  have eq1701 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X3) ◇ ((((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X3))) := superpose eq1533 eq1700
  have eq1703 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ (X2 ◇ X3)) := superpose eq1533 eq1682
  have eq1707 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X3))) := superpose eq1703 eq1701
  have eq1711 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ X3) ◇ (X1 ◇ X3)) := superpose eq1703 eq1707
  have eq1712 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1692 eq1711
  have eq1713 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1712 eq1533
  have eq1747 (X0 X1 : G) : X0 = X1 := superpose eq1712 eq1713
  have eq1766 (X0 : G) : sK0 ≠ X0 := superpose eq1747 eq8
  subsumption eq1766 eq1747


@[equational_result]
theorem Equation26039_implies_Equation2 (G : Type*) [Magma G] (h : Equation26039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X2))) = X2 := superpose eq7 eq9
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = X2 := superpose eq18 eq11
  have eq37 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) = X0 := superpose eq7 eq10
  have eq58 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq37 eq20
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq58 eq58
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq106 eq65


@[equational_result]
theorem Equation26040_implies_Equation2 (G : Type*) [Magma G] (h : Equation26040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X4)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq24 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq10 eq10
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq24 eq24
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq11 eq49
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq126 eq68


@[equational_result]
theorem Equation26042_implies_Equation2 (G : Type*) [Magma G] (h : Equation26042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation26044_implies_Equation2 (G : Type*) [Magma G] (h : Equation26044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X4)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq71 eq19


@[equational_result]
theorem Equation26048_implies_Equation2 (G : Type*) [Magma G] (h : Equation26048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation26050_implies_Equation2 (G : Type*) [Magma G] (h : Equation26050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X4 ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq42 eq18


@[equational_result]
theorem Equation26051_implies_Equation2 (G : Type*) [Magma G] (h : Equation26051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X4 ◇ ((X0 ◇ X2) ◇ X3))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq38 (X0 X6 : G) : X0 = X6 := superpose eq11 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq48 eq38


@[equational_result]
theorem Equation26052_implies_Equation2 (G : Type*) [Magma G] (h : Equation26052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X1 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq58 eq14


@[equational_result]
theorem Equation26053_implies_Equation2 (G : Type*) [Magma G] (h : Equation26053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation26056_implies_Equation2 (G : Type*) [Magma G] (h : Equation26056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X3)) = ((X1 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X3)) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq12 eq10
  have eq37 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X2 := superpose eq15 eq9
  have eq49 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq9 eq12
  have eq81 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq49 eq37
  have eq115 (X0 X2 : G) : X0 = X2 := superpose eq9 eq81
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq115 eq8
  subsumption eq157 eq115


@[equational_result]
theorem Equation26057_implies_Equation2 (G : Type*) [Magma G] (h : Equation26057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X3)) = ((X1 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X4) ◇ X4)) ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) ◇ X0) := superpose eq10 eq7
  have eq34 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) = X0 := superpose eq10 eq11
  have eq41 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ X0) := superpose eq34 eq18
  have eq76 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq10 eq41
  have eq87 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq76 eq34
  have eq98 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq87 eq87
  have eq107 (X0 X3 : G) : X0 = X3 := superpose eq10 eq98
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq151 eq107


@[equational_result]
theorem Equation26060_implies_Equation2 (G : Type*) [Magma G] (h : Equation26060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X3)) = ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = ((((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq78 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2)) = X0 := superpose eq7 eq9
  have eq110 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq18 eq78
  have eq172 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X0 ◇ (X2 ◇ X4)) ◇ (X2 ◇ X4))) = (X1 ◇ ((X0 ◇ ((X1 ◇ X3) ◇ X3)) ◇ X3)) := superpose eq12 eq11
  have eq197 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) := superpose eq110 eq12
  have eq198 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq110 eq78
  have eq214 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq110 eq197
  have eq215 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq7 eq214
  have eq325 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1)) = X2 := superpose eq215 eq11
  have eq326 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2)) = X2 := superpose eq215 eq11
  have eq336 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq215 eq11
  have eq380 (X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) = X2 := superpose eq336 eq325
  have eq386 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq380 eq198
  have eq399 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2)) = X2 := superpose eq386 eq326
  have eq413 (X0 X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X4)) ◇ ((X0 ◇ (X2 ◇ X4)) ◇ (X2 ◇ X4))) = X3 := superpose eq399 eq172
  have eq419 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq413 eq12
  have eq641 (X0 X2 : G) : X0 = X2 := superpose eq419 eq419
  have eq649 (X0 : G) : sK0 ≠ X0 := superpose eq641 eq8
  subsumption eq649 eq641


@[equational_result]
theorem Equation26061_implies_Equation2 (G : Type*) [Magma G] (h : Equation26061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X3)) := superpose eq7 eq7
  have eq32 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := superpose eq10 eq7
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4))) ◇ (X2 ◇ X5)) := superpose eq10 eq7
  have eq35 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq32 eq34
  have eq36 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = X0 := superpose eq35 eq7
  have eq58 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq35 eq36
  have eq59 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq35 eq58
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq59 eq59
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq62 eq60


@[equational_result]
theorem Equation26064_implies_Equation2 (G : Type*) [Magma G] (h : Equation26064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X3)) = ((X1 ◇ (X0 ◇ (X3 ◇ X3))) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2)) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (((X0 ◇ (X3 ◇ X3)) ◇ X3) ◇ X3)) ◇ (((X0 ◇ (X3 ◇ X3)) ◇ X3) ◇ X3))) = X2 := superpose eq23 eq23
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq23 eq33
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq7 eq50
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq148 eq51


@[equational_result]
theorem Equation26065_implies_Equation2 (G : Type*) [Magma G] (h : Equation26065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq81 eq15


@[equational_result]
theorem Equation26067_implies_Equation2 (G : Type*) [Magma G] (h : Equation26067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq67 eq19


@[equational_result]
theorem Equation26068_implies_Equation2 (G : Type*) [Magma G] (h : Equation26068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq64 eq16


@[equational_result]
theorem Equation26069_implies_Equation2 (G : Type*) [Magma G] (h : Equation26069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq10 eq10
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq153 eq61


@[equational_result]
theorem Equation26070_implies_Equation2 (G : Type*) [Magma G] (h : Equation26070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation26072_implies_Equation2 (G : Type*) [Magma G] (h : Equation26072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ X4)))) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq14 eq11
  have eq29 (X0 X1 : G) : X0 = X1 := superpose eq10 eq21
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq33 eq29


@[equational_result]
theorem Equation26073_implies_Equation2 (G : Type*) [Magma G] (h : Equation26073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq17 (X0 X2 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ (((X0 ◇ X2) ◇ X5) ◇ X6))) = X4 := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq9
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X4) ◇ X5)) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq33 (X0 X1 X3 X4 X5 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X4) ◇ X5)) = X0 := superpose eq23 eq26
  have eq34 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq33 eq17
  have eq47 (X0 X2 : G) : X0 = X2 := superpose eq10 eq34
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq63 eq47


@[equational_result]
theorem Equation26074_implies_Equation2 (G : Type*) [Magma G] (h : Equation26074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X4))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq21 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X0 ◇ X3) ◇ X5))) = X4 := superpose eq7 eq10
  have eq33 (X0 X1 X2 X4 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq10 eq11
  have eq42 (X0 X3 X4 : G) : (X0 ◇ (X0 ◇ X3)) = X4 := superpose eq33 eq21
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq42 eq42
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq96 eq51


@[equational_result]
theorem Equation26075_implies_Equation2 (G : Type*) [Magma G] (h : Equation26075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X6)) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq10
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq10 eq36
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq98 eq57


@[equational_result]
theorem Equation26077_implies_Equation2 (G : Type*) [Magma G] (h : Equation26077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq83 eq19


@[equational_result]
theorem Equation26078_implies_Equation2 (G : Type*) [Magma G] (h : Equation26078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X3) ◇ X4))) = X2 := superpose eq7 eq7
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq62 eq25


@[equational_result]
theorem Equation26079_implies_Equation2 (G : Type*) [Magma G] (h : Equation26079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq48 eq19


@[equational_result]
theorem Equation26080_implies_Equation2 (G : Type*) [Magma G] (h : Equation26080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X6)) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation26082_implies_Equation2 (G : Type*) [Magma G] (h : Equation26082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X3) ◇ X4) ◇ X1)) = X2 := superpose eq7 eq7
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq63 eq25


@[equational_result]
theorem Equation26083_implies_Equation2 (G : Type*) [Magma G] (h : Equation26083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation26084_implies_Equation2 (G : Type*) [Magma G] (h : Equation26084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq70 eq16


@[equational_result]
theorem Equation26085_implies_Equation2 (G : Type*) [Magma G] (h : Equation26085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X6 : G) : (X0 ◇ (X3 ◇ X6)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq66 eq16


@[equational_result]
theorem Equation26087_implies_Equation2 (G : Type*) [Magma G] (h : Equation26087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ ((X4 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation26088_implies_Equation2 (G : Type*) [Magma G] (h : Equation26088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq70 eq16


@[equational_result]
theorem Equation26089_implies_Equation2 (G : Type*) [Magma G] (h : Equation26089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation26090_implies_Equation2 (G : Type*) [Magma G] (h : Equation26090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation26092_implies_Equation2 (G : Type*) [Magma G] (h : Equation26092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : ((X1 ◇ X0) ◇ (X6 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation26093_implies_Equation2 (G : Type*) [Magma G] (h : Equation26093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X6 ◇ X5)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq66 eq16


@[equational_result]
theorem Equation26094_implies_Equation2 (G : Type*) [Magma G] (h : Equation26094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X6 : G) : (X0 ◇ (X6 ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation26095_implies_Equation2 (G : Type*) [Magma G] (h : Equation26095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X6 : G) : (X0 ◇ (X6 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation26096_implies_Equation2 (G : Type*) [Magma G] (h : Equation26096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X4 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation26102_implies_Equation2 (G : Type*) [Magma G] (h : Equation26102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3)) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) := superpose eq7 eq9
  have eq32 (X0 X1 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ X3)) = X0 := superpose eq7 eq23
  have eq36 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ X3)) := superpose eq7 eq23
  have eq71 (X0 X1 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ X3)) = X0 := superpose eq7 eq32
  have eq73 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) = X0 := superpose eq71 eq36
  have eq75 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq73 eq23
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq75 eq7
  have eq150 (X0 X3 : G) : X0 = X3 := superpose eq93 eq93
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq150 eq8
  subsumption eq152 eq150


@[equational_result]
theorem Equation26104_implies_Equation2 (G : Type*) [Magma G] (h : Equation26104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq7 eq7
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq27
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq101 eq33


@[equational_result]
theorem Equation26106_implies_Equation2 (G : Type*) [Magma G] (h : Equation26106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation26112_implies_Equation2 (G : Type*) [Magma G] (h : Equation26112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))))) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X3)) = X2 := superpose eq10 eq7
  have eq40 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ (X2 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X3)) ◇ X1) = X4 := superpose eq9 eq10
  have eq46 (X1 X4 : G) : (X1 ◇ X1) = X4 := superpose eq16 eq40
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq7 eq46
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq138 eq48


@[equational_result]
theorem Equation26114_implies_Equation2 (G : Type*) [Magma G] (h : Equation26114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))))) ◇ X4) = X3 := superpose eq10 eq10
  have eq21 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq10 eq12
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq159 eq50


@[equational_result]
theorem Equation26116_implies_Equation2 (G : Type*) [Magma G] (h : Equation26116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation26122_implies_Equation2 (G : Type*) [Magma G] (h : Equation26122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ X1))) := superpose eq10 eq13
  have eq29 (X0 X3 : G) : (X0 ◇ X0) = (X0 ◇ X3) := superpose eq7 eq28
  have eq31 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq29 eq7
  have eq45 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq54 eq45


@[equational_result]
theorem Equation26124_implies_Equation2 (G : Type*) [Magma G] (h : Equation26124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ X4)) ◇ X0) = X3 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) = X0 := superpose eq7 eq10
  have eq34 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq21 eq11
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq34
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq60 eq38


@[equational_result]
theorem Equation26128_implies_Equation2 (G : Type*) [Magma G] (h : Equation26128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X0) ◇ X4)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 X5 X6 : G) : (X0 ◇ X4) = (X0 ◇ ((X4 ◇ X5) ◇ X6)) := superpose eq7 eq10
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) ◇ X0) = X2 := superpose eq12 eq11
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq12 eq24
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq48 eq38


@[equational_result]
theorem Equation26130_implies_Equation2 (G : Type*) [Magma G] (h : Equation26130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) = X3 := superpose eq7 eq7
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq76 eq57


@[equational_result]
theorem Equation26131_implies_Equation2 (G : Type*) [Magma G] (h : Equation26131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation26132_implies_Equation2 (G : Type*) [Magma G] (h : Equation26132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation26133_implies_Equation2 (G : Type*) [Magma G] (h : Equation26133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation26136_implies_Equation2 (G : Type*) [Magma G] (h : Equation26136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq11 eq14
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq51 eq32


@[equational_result]
theorem Equation26139_implies_Equation2 (G : Type*) [Magma G] (h : Equation26139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq10
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq7 eq16
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq78 eq55


@[equational_result]
theorem Equation26141_implies_Equation2 (G : Type*) [Magma G] (h : Equation26141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq9 eq10
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq35 eq27


@[equational_result]
theorem Equation26142_implies_Equation2 (G : Type*) [Magma G] (h : Equation26142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) = (X0 ◇ (X2 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X2 ◇ X2)) := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq9 eq9
  have eq14 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X3)) := superpose eq9 eq9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X0)))) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X0))))) = X0 := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X1))) = X3 := superpose eq9 eq7
  have eq23 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq12 eq13
  have eq26 (X0 X1 X2 X4 : G) : (X2 ◇ (X4 ◇ X4)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq14
  have eq75 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq23
  have eq249 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq18
  have eq297 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X1))) = X3 := superpose eq249 eq15
  have eq306 (X2 X4 : G) : (X2 ◇ (X4 ◇ X4)) = X2 := superpose eq297 eq26
  have eq315 (X0 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ X0) := superpose eq306 eq75
  have eq324 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq315 eq16
  have eq331 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq306 eq324
  have eq335 (X0 X2 : G) : X0 = X2 := superpose eq331 eq331
  have eq375 (X0 : G) : sK0 ≠ X0 := superpose eq335 eq8
  subsumption eq375 eq335


@[equational_result]
theorem Equation26143_implies_Equation2 (G : Type*) [Magma G] (h : Equation26143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation26146_implies_Equation2 (G : Type*) [Magma G] (h : Equation26146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq51 eq32


@[equational_result]
theorem Equation26148_implies_Equation2 (G : Type*) [Magma G] (h : Equation26148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation26149_implies_Equation2 (G : Type*) [Magma G] (h : Equation26149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26151_implies_Equation2 (G : Type*) [Magma G] (h : Equation26151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26152_implies_Equation2 (G : Type*) [Magma G] (h : Equation26152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation26153_implies_Equation2 (G : Type*) [Magma G] (h : Equation26153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26155_implies_Equation2 (G : Type*) [Magma G] (h : Equation26155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X3)) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq10 eq10
  have eq21 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq10 eq7
  have eq35 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) ◇ ((((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0)) ◇ X4)) = (((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq10 eq9
  have eq36 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) ◇ X3)) ◇ X0) = (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq10 eq9
  have eq38 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq10
  have eq41 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) = X3 := superpose eq9 eq7
  have eq44 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) = (((X3 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) ◇ (((X3 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) ◇ (X3 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))))) ◇ X4)) ◇ X3) := superpose eq9 eq10
  have eq46 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) ◇ X3)) = ((X0 ◇ ((X0 ◇ X0) ◇ X4)) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := superpose eq9 eq10
  have eq48 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (((X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) ◇ X3)) ◇ X0) := superpose eq9 eq36
  have eq50 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq48 eq44
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2)) := superpose eq50 eq38
  have eq113 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X4)) ◇ ((X2 ◇ X0) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3))) ◇ (X5 ◇ X2)) = X5 := superpose eq10 eq21
  have eq148 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0))) = X3 := superpose eq21 eq7
  have eq153 (X0 X1 X2 X3 X5 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X2 ◇ X0) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3))) ◇ (X5 ◇ X2)) = X5 := superpose eq51 eq113
  have eq159 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) = X3 := superpose eq7 eq41
  have eq184 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq20 eq41
  have eq188 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) ◇ X3)) := superpose eq20 eq41
  have eq195 (X0 X1 X2 X3 : G) : (((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X3 ◇ X2)) = X3 := superpose eq41 eq21
  have eq217 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X2)) = ((X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) ◇ X3)) := superpose eq159 eq46
  have eq225 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X2)) = ((X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ (X0 ◇ X3)) := superpose eq159 eq217
  have eq229 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0)) = (((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq188 eq35
  have eq230 (X0 X1 X2 X5 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X2 ◇ X0))) ◇ (X5 ◇ X2)) = X5 := superpose eq229 eq153
  have eq231 (X2 X5 : G) : ((X2 ◇ X2) ◇ (X5 ◇ X2)) = X5 := superpose eq7 eq230
  have eq239 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0))) = X3 := superpose eq231 eq148
  have eq241 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq231 eq184
  have eq271 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (((X3 ◇ ((X3 ◇ X3) ◇ X4)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X0) := superpose eq7 eq225
  have eq280 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) = X0 := superpose eq7 eq225
  have eq318 (X0 X2 X3 : G) : (X2 ◇ ((X2 ◇ X2) ◇ X3)) = (((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) ◇ ((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0)) := superpose eq271 eq229
  have eq337 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X3 ◇ X2)) = X3 := superpose eq318 eq195
  have eq344 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq231 eq280
  have eq350 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq344 eq239
  have eq352 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq344 eq241
  have eq361 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq344 eq350
  have eq367 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq352 eq337
  have eq415 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq367 eq361
  have eq446 (X0 X2 : G) : X0 = X2 := superpose eq415 eq415
  have eq457 (X0 : G) : sK0 ≠ X0 := superpose eq446 eq8
  subsumption eq457 eq446


@[equational_result]
theorem Equation26157_implies_Equation2 (G : Type*) [Magma G] (h : Equation26157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq52 eq33


@[equational_result]
theorem Equation26159_implies_Equation2 (G : Type*) [Magma G] (h : Equation26159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation26160_implies_Equation2 (G : Type*) [Magma G] (h : Equation26160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26161_implies_Equation2 (G : Type*) [Magma G] (h : Equation26161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26163_implies_Equation2 (G : Type*) [Magma G] (h : Equation26163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26164_implies_Equation2 (G : Type*) [Magma G] (h : Equation26164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation26165_implies_Equation2 (G : Type*) [Magma G] (h : Equation26165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26167_implies_Equation2 (G : Type*) [Magma G] (h : Equation26167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26168_implies_Equation2 (G : Type*) [Magma G] (h : Equation26168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26169_implies_Equation2 (G : Type*) [Magma G] (h : Equation26169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26170_implies_Equation2 (G : Type*) [Magma G] (h : Equation26170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26172_implies_Equation2 (G : Type*) [Magma G] (h : Equation26172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ X3)) ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq10 eq10
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0)))) = X1 := superpose eq7 eq9
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq22 eq22
  have eq102 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq39 eq39
  have eq125 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq102 eq15
  have eq126 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq102 eq13
  have eq127 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq102 eq10
  have eq132 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq102 eq125
  have eq133 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq102 eq126
  have eq164 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X2 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq127 eq39
  have eq165 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq133 eq164
  have eq166 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq39 eq165
  have eq167 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq166 eq132
  have eq234 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X1))) = X2 := superpose eq167 eq39
  have eq242 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq167 eq234
  have eq243 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq167 eq242
  have eq250 (X0 X1 : G) : X0 = X1 := superpose eq167 eq243
  have eq255 (X0 : G) : sK0 ≠ X0 := superpose eq250 eq8
  subsumption eq255 eq250


@[equational_result]
theorem Equation26174_implies_Equation2 (G : Type*) [Magma G] (h : Equation26174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ X4)) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation26176_implies_Equation2 (G : Type*) [Magma G] (h : Equation26176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq85 eq39


@[equational_result]
theorem Equation26177_implies_Equation2 (G : Type*) [Magma G] (h : Equation26177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq28 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq28 eq28
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq89 eq35


@[equational_result]
theorem Equation26178_implies_Equation2 (G : Type*) [Magma G] (h : Equation26178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ X0) ◇ (X1 ◇ X4)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq145 eq61


@[equational_result]
theorem Equation26180_implies_Equation2 (G : Type*) [Magma G] (h : Equation26180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ X3)) ◇ ((X2 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X0))) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = ((X0 ◇ X1) ◇ ((((X1 ◇ X3) ◇ X2) ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) ◇ (X1 ◇ X3))) := superpose eq10 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ X3) ◇ (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X2))) := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq10
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq7
  have eq43 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X1 ◇ X2)))) := superpose eq10 eq19
  have eq50 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq19 eq19
  have eq53 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq19 eq7
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X2) := superpose eq19 eq11
  have eq57 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) := superpose eq19 eq10
  have eq62 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X2) := superpose eq7 eq54
  have eq67 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X4 ◇ ((X4 ◇ X3) ◇ X5))) ◇ X0)))) ◇ X0) ◇ ((X2 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X4 ◇ ((X4 ◇ X3) ◇ X5))) ◇ X0)))))) = X5 := superpose eq11 eq9
  have eq68 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq7 eq9
  have eq101 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq50 eq10
  have eq102 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq50 eq9
  have eq117 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq101 eq50
  have eq118 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq117 eq101
  have eq120 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) = X1 := superpose eq16 eq102
  have eq121 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := superpose eq53 eq120
  have eq122 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq118 eq121
  have eq123 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := superpose eq118 eq122
  have eq124 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq118 eq123
  have eq178 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq68 eq7
  have eq184 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) = ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq68 eq10
  have eq188 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1))) := superpose eq68 eq19
  have eq209 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq178 eq68
  have eq219 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq62 eq184
  have eq220 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) := superpose eq219 eq15
  have eq225 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)))) := superpose eq220 eq43
  have eq235 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq62 eq188
  have eq236 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq178 eq235
  have eq263 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq118 eq7
  have eq280 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose eq209 eq209
  have eq289 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X1)) = (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq209 eq10
  have eq307 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq219 eq289
  have eq310 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose eq307 eq280
  have eq323 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) := superpose eq10 eq124
  have eq351 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) := superpose eq323 eq225
  have eq357 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq351
  have eq358 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ X2) ◇ X1) := superpose eq118 eq357
  have eq359 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq358 eq10
  have eq360 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = ((X0 ◇ X1) ◇ ((((X1 ◇ X3) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X3))) := superpose eq358 eq13
  have eq381 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq359 eq53
  have eq382 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq359 eq57
  have eq394 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq381 eq236
  have eq422 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose eq394 eq310
  have eq443 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq381 eq382
  have eq444 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq359 eq443
  have eq445 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq444 eq422
  have eq455 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) := superpose eq358 eq360
  have eq456 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq455 eq394
  have eq473 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq456 eq445
  have eq476 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq473 eq263
  have eq505 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X0)))) ◇ X0) ◇ ((X2 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X0)))))) = X5 := superpose eq476 eq67
  have eq626 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X0)))) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X0))))) = X5 := superpose eq476 eq505
  have eq627 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X0))) ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X0)))) = X5 := superpose eq476 eq626
  have eq628 (X0 X3 X4 X5 : G) : ((((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X0)) ◇ X0) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X0))) = X5 := superpose eq476 eq627
  have eq629 (X0 X3 X4 X5 : G) : (((((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X0) ◇ X0) ◇ (((X3 ◇ X4) ◇ (X4 ◇ X5)) ◇ X0)) = X5 := superpose eq476 eq628
  have eq630 (X0 X5 : G) : ((X0 ◇ X0) ◇ X0) = X5 := superpose eq476 eq629
  have eq631 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq118 eq630
  have eq674 (X0 X2 : G) : X0 = X2 := superpose eq631 eq631
  have eq679 (X0 : G) : sK0 ≠ X0 := superpose eq674 eq8
  subsumption eq679 eq674


@[equational_result]
theorem Equation26181_implies_Equation2 (G : Type*) [Magma G] (h : Equation26181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((((X2 ◇ X3) ◇ X1) ◇ (((X2 ◇ X0) ◇ X3) ◇ ((X2 ◇ X0) ◇ X3))) ◇ (((X2 ◇ X3) ◇ X1) ◇ (((X2 ◇ X0) ◇ X3) ◇ ((X2 ◇ X0) ◇ X3))))) := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq18 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose eq10 eq7
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((((X2 ◇ X3) ◇ X1) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) ◇ (((X2 ◇ X3) ◇ X1) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))))) := superpose eq15 eq12
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) := superpose eq15 eq10
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))))) := superpose eq15 eq21
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))))) := superpose eq15 eq25
  have eq34 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq22 eq22
  have eq40 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq18
  have eq51 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq18 eq7
  have eq57 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq51 eq34
  have eq61 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))))) := superpose eq57 eq26
  have eq64 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := superpose eq57 eq40
  have eq89 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)))) := superpose eq57 eq61
  have eq90 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3))) := superpose eq57 eq89
  have eq91 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X0 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X0) ◇ X3))) := superpose eq57 eq90
  have eq92 (X0 X1 X2 X3 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ ((X2 ◇ X0) ◇ X3))) = X1 := superpose eq57 eq91
  have eq99 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq57 eq64
  have eq100 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq57 eq99
  have eq102 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) = X1 := superpose eq100 eq92
  have eq109 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X1 := superpose eq100 eq102
  have eq110 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq100 eq109
  have eq111 (X0 X1 : G) : X0 = X1 := superpose eq57 eq110
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq111 eq8
  subsumption eq119 eq111


@[equational_result]
theorem Equation26182_implies_Equation2 (G : Type*) [Magma G] (h : Equation26182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq49 (X0 X1 X2 X3 X5 X6 : G) : (((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X6)) ◇ X5) = X6 := superpose eq10 eq11
  have eq51 (X0 X1 X2 X3 X6 X7 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X1) ◇ X3)) ◇ X7)) ◇ X6) = X7 := superpose eq10 eq11
  have eq72 (X2 X3 X6 X7 : G) : ((X2 ◇ X3) ◇ X6) = X7 := superpose eq49 eq51
  have eq193 (X0 X4 : G) : X0 = X4 := superpose eq7 eq72
  have eq340 (X0 : G) : sK0 ≠ X0 := superpose eq193 eq8
  subsumption eq340 eq193


@[equational_result]
theorem Equation26184_implies_Equation2 (G : Type*) [Magma G] (h : Equation26184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X3 ◇ X1) = ((X1 ◇ X0) ◇ (X4 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0)))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) = (X0 ◇ (X5 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0)))) := superpose eq7 eq10
  have eq34 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) = X2 := superpose eq11 eq16
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq34 eq11
  have eq37 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq35 eq12
  have eq43 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq35 eq37
  have eq45 (X0 X1 : G) : X0 = X1 := superpose eq35 eq43
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq47 eq45


@[equational_result]
theorem Equation26185_implies_Equation2 (G : Type*) [Magma G] (h : Equation26185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation26186_implies_Equation2 (G : Type*) [Magma G] (h : Equation26186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X3 ◇ X3) = ((X1 ◇ X0) ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq93 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq93 eq8
  subsumption eq145 eq93


@[equational_result]
theorem Equation26187_implies_Equation2 (G : Type*) [Magma G] (h : Equation26187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 X6 X7 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ X5)) ◇ (X6 ◇ X7)) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X5 := superpose eq7 eq9
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation26189_implies_Equation2 (G : Type*) [Magma G] (h : Equation26189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X3) ◇ X1)) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) = (((X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ (((X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X4) ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))))) ◇ X3) := superpose eq7 eq10
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1))) = (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X1) := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X2 ◇ X4) ◇ X2)) = ((((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq10 eq10
  have eq23 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq10 eq7
  have eq28 (X0 X1 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) = X3 := superpose eq7 eq9
  have eq40 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))))) = (((X4 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))))) ◇ (((X4 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))))) ◇ X5) ◇ (X4 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))))))) ◇ X4) := superpose eq9 eq10
  have eq65 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X0) ◇ ((((X0 ◇ X2) ◇ X0) ◇ X3) ◇ ((X0 ◇ X2) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq22 eq7
  have eq99 (X0 X1 X2 X3 X5 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) ◇ X1) ◇ (X5 ◇ X2)) = X5 := superpose eq10 eq23
  have eq106 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1) ◇ X0) = (((X4 ◇ X2) ◇ (((X4 ◇ X2) ◇ X5) ◇ (X4 ◇ X2))) ◇ X4) := superpose eq23 eq23
  have eq109 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X0) = (((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X3) := superpose eq23 eq9
  have eq129 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X0) := superpose eq7 eq28
  have eq133 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = ((((X1 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X1))) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X1))) := superpose eq28 eq10
  have eq135 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X3) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))))) ◇ X0) = ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) := superpose eq28 eq7
  have eq143 (X0 X1 X2 : G) : ((((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq129 eq65
  have eq145 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X1) = (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) ◇ X1) := superpose eq129 eq15
  have eq147 (X0 X1 X3 X4 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X3) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X0) := superpose eq145 eq109
  have eq151 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) = ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) := superpose eq135 eq11
  have eq158 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1))) = (((X4 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1)) ◇ (((X4 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1)) ◇ X5) ◇ (X4 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1)))) ◇ X4) := superpose eq151 eq40
  have eq169 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1))) = (((X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1)) ◇ X1) ◇ X1) := superpose eq147 eq158
  have eq173 (X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = ((((X1 ◇ ((X1 ◇ ((X1 ◇ X3) ◇ X1)) ◇ X1)) ◇ X1) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X1))) := superpose eq169 eq133
  have eq179 (X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = X1 := superpose eq143 eq173
  have eq180 (X0 X1 X2 X4 X5 : G) : (((X4 ◇ X2) ◇ (((X4 ◇ X2) ◇ X5) ◇ (X4 ◇ X2))) ◇ X4) = (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0) := superpose eq179 eq106
  have eq181 (X0 X1 X2 X5 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ (X5 ◇ X2)) = X5 := superpose eq179 eq99
  have eq183 (X0 X1 X2 X4 : G) : (X2 ◇ ((X2 ◇ X4) ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) := superpose eq179 eq21
  have eq224 (X0 X1 X2 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0) = ((X4 ◇ X2) ◇ X4) := superpose eq179 eq180
  have eq225 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X2 := superpose eq179 eq183
  have eq226 (X2 X5 : G) : (X2 ◇ (X5 ◇ X2)) = X5 := superpose eq225 eq181
  have eq227 (X2 X4 : G) : ((X4 ◇ X2) ◇ X4) = X2 := superpose eq225 eq224
  have eq230 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq227 eq179
  have eq232 (X2 X5 : G) : (X2 ◇ X5) = X5 := superpose eq230 eq226
  have eq335 (X0 X1 : G) : X0 = X1 := superpose eq230 eq232
  have eq345 (X0 : G) : sK0 ≠ X0 := superpose eq335 eq8
  subsumption eq345 eq335


@[equational_result]
theorem Equation26191_implies_Equation2 (G : Type*) [Magma G] (h : Equation26191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1)))) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq13 eq16
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation26193_implies_Equation2 (G : Type*) [Magma G] (h : Equation26193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26194_implies_Equation2 (G : Type*) [Magma G] (h : Equation26194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation26195_implies_Equation2 (G : Type*) [Magma G] (h : Equation26195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26197_implies_Equation2 (G : Type*) [Magma G] (h : Equation26197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26198_implies_Equation2 (G : Type*) [Magma G] (h : Equation26198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26199_implies_Equation2 (G : Type*) [Magma G] (h : Equation26199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26201_implies_Equation2 (G : Type*) [Magma G] (h : Equation26201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26202_implies_Equation2 (G : Type*) [Magma G] (h : Equation26202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26203_implies_Equation2 (G : Type*) [Magma G] (h : Equation26203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26204_implies_Equation2 (G : Type*) [Magma G] (h : Equation26204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26208_implies_Equation2 (G : Type*) [Magma G] (h : Equation26208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq13 eq16
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation26210_implies_Equation2 (G : Type*) [Magma G] (h : Equation26210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26211_implies_Equation2 (G : Type*) [Magma G] (h : Equation26211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation26212_implies_Equation2 (G : Type*) [Magma G] (h : Equation26212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26214_implies_Equation2 (G : Type*) [Magma G] (h : Equation26214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26215_implies_Equation2 (G : Type*) [Magma G] (h : Equation26215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26216_implies_Equation2 (G : Type*) [Magma G] (h : Equation26216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26218_implies_Equation2 (G : Type*) [Magma G] (h : Equation26218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26219_implies_Equation2 (G : Type*) [Magma G] (h : Equation26219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26220_implies_Equation2 (G : Type*) [Magma G] (h : Equation26220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26221_implies_Equation2 (G : Type*) [Magma G] (h : Equation26221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26223_implies_Equation2 (G : Type*) [Magma G] (h : Equation26223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))) = X4 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq10 eq10
  have eq21 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq14 eq13
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq134 eq63


@[equational_result]
theorem Equation26224_implies_Equation2 (G : Type*) [Magma G] (h : Equation26224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ (X5 ◇ (X0 ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq10
  have eq25 (X0 X2 X5 : G) : (X0 ◇ (X5 ◇ (X0 ◇ X2))) = X5 := superpose eq17 eq9
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq25 eq25
  have eq44 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq28 eq25
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq44 eq44
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq71 eq55


@[equational_result]
theorem Equation26225_implies_Equation2 (G : Type*) [Magma G] (h : Equation26225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) = X4 := superpose eq10 eq10
  have eq23 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X4)) = X5 := superpose eq16 eq9
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq23 eq23
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq23 eq32
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq56 eq33


@[equational_result]
theorem Equation26226_implies_Equation2 (G : Type*) [Magma G] (h : Equation26226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ X5)) ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq13 eq16
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq55 eq36


@[equational_result]
theorem Equation26228_implies_Equation2 (G : Type*) [Magma G] (h : Equation26228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26229_implies_Equation2 (G : Type*) [Magma G] (h : Equation26229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26230_implies_Equation2 (G : Type*) [Magma G] (h : Equation26230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26231_implies_Equation2 (G : Type*) [Magma G] (h : Equation26231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26233_implies_Equation2 (G : Type*) [Magma G] (h : Equation26233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26234_implies_Equation2 (G : Type*) [Magma G] (h : Equation26234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26235_implies_Equation2 (G : Type*) [Magma G] (h : Equation26235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26236_implies_Equation2 (G : Type*) [Magma G] (h : Equation26236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26238_implies_Equation2 (G : Type*) [Magma G] (h : Equation26238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26239_implies_Equation2 (G : Type*) [Magma G] (h : Equation26239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26240_implies_Equation2 (G : Type*) [Magma G] (h : Equation26240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26241_implies_Equation2 (G : Type*) [Magma G] (h : Equation26241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26243_implies_Equation2 (G : Type*) [Magma G] (h : Equation26243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26244_implies_Equation2 (G : Type*) [Magma G] (h : Equation26244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26245_implies_Equation2 (G : Type*) [Magma G] (h : Equation26245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26246_implies_Equation2 (G : Type*) [Magma G] (h : Equation26246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26247_implies_Equation2 (G : Type*) [Magma G] (h : Equation26247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26253_implies_Equation2 (G : Type*) [Magma G] (h : Equation26253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq7 eq9
  have eq29 (X0 X1 X2 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ X4)) ◇ X2) = X4 := superpose eq10 eq10
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ X0)) ◇ X2) := superpose eq9 eq10
  have eq34 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X4 ◇ X0) ◇ X0)) ◇ ((((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X4 ◇ X0) ◇ X0)))) = X3 := superpose eq10 eq7
  have eq36 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = (X0 ◇ (((((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X1)))) ◇ ((X4 ◇ X0) ◇ X0)) ◇ ((((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X1)))) ◇ ((X4 ◇ X0) ◇ X0)))) := superpose eq10 eq9
  have eq37 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq29 eq30
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq7 eq37
  have eq41 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq37
  have eq42 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq37
  have eq53 (X0 X1 X3 X4 : G) : (X1 ◇ X1) = (X0 ◇ ((((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))) ◇ ((X4 ◇ X0) ◇ X0)) ◇ (((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))) ◇ ((X4 ◇ X0) ◇ X0)))) := superpose eq39 eq36
  have eq54 (X0 X2 X3 X4 : G) : (X0 ◇ (((((X2 ◇ X3) ◇ X3) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X4 ◇ X0) ◇ X0)) ◇ ((((X2 ◇ X3) ◇ X3) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X4 ◇ X0) ◇ X0)))) = X3 := superpose eq39 eq34
  have eq59 (X0 X3 X4 : G) : (X0 ◇ (((X3 ◇ X3) ◇ ((X4 ◇ X0) ◇ X0)) ◇ ((X3 ◇ X3) ◇ ((X4 ◇ X0) ◇ X0)))) = X3 := superpose eq39 eq54
  have eq60 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq59 eq15
  have eq61 (X0 X1 X3 X4 : G) : (X1 ◇ X1) = (X0 ◇ (((X3 ◇ (X1 ◇ X1)) ◇ ((X4 ◇ X0) ◇ X0)) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ ((X4 ◇ X0) ◇ X0)))) := superpose eq60 eq53
  have eq75 (X0 X1 X3 X4 : G) : (X1 ◇ X1) = (X0 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ ((X4 ◇ X0) ◇ X0))) := superpose eq60 eq61
  have eq76 (X0 X1 X3 X4 : G) : (X0 ◇ ((X3 ◇ X1) ◇ ((X4 ◇ X0) ◇ X0))) = X1 := superpose eq60 eq75
  have eq90 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X1) ◇ X0)) = X1 := superpose eq41 eq76
  have eq92 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq60 eq42
  have eq94 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq92 eq90
  have eq113 (X0 X2 : G) : X0 = X2 := superpose eq94 eq94
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq113 eq8
  subsumption eq121 eq113


@[equational_result]
theorem Equation26254_implies_Equation2 (G : Type*) [Magma G] (h : Equation26254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq27 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) := superpose eq7 eq11
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq11
  have eq115 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) = ((X3 ◇ X0) ◇ (X3 ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)))) := superpose eq11 eq9
  have eq144 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq27 eq9
  have eq162 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq28 eq9
  have eq163 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose eq28 eq9
  have eq165 (X0 X1 : G) : (((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq28 eq7
  have eq176 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq115 eq162
  have eq177 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq176
  have eq178 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq177 eq144
  have eq179 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq177 eq28
  have eq180 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq177 eq178
  have eq187 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose eq177 eq163
  have eq188 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq177 eq187
  have eq189 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq177 eq188
  have eq191 (X0 X1 : G) : (((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq177 eq165
  have eq204 (X0 X1 : G) : ((X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq179 eq12
  have eq242 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq177 eq9
  have eq249 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0)) := superpose eq177 eq11
  have eq255 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq180 eq242
  have eq266 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq255 eq204
  have eq291 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq266 eq249
  have eq343 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq291 eq177
  have eq344 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X1 := superpose eq291 eq179
  have eq407 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq343 eq10
  have eq500 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) ◇ ((((((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) ◇ X3) ◇ X3)) ◇ X2) = X3 := superpose eq407 eq12
  have eq534 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) ◇ ((((X2 ◇ X2) ◇ X1) ◇ X3) ◇ X3)) ◇ X2) = X3 := superpose eq255 eq500
  have eq754 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq291 eq180
  have eq767 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq180 eq7
  have eq785 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq754 eq767
  have eq786 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq255 eq785
  have eq792 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq786 eq189
  have eq793 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq786 eq191
  have eq845 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq786 eq792
  have eq846 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq343 eq845
  have eq852 (X0 X1 : G) : (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq846 eq793
  have eq853 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq344 eq852
  have eq855 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((((X2 ◇ X2) ◇ X1) ◇ X3) ◇ X3)) ◇ X2) = X3 := superpose eq853 eq534
  have eq1025 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) = X3 := superpose eq853 eq855
  have eq1026 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq853 eq1025
  have eq1033 (X0 X3 : G) : X0 = X3 := superpose eq1026 eq1026
  have eq1042 (X0 : G) : sK0 ≠ X0 := superpose eq1033 eq8
  subsumption eq1042 eq1033


@[equational_result]
theorem Equation26255_implies_Equation2 (G : Type*) [Magma G] (h : Equation26255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X2 ◇ X4) = ((X1 ◇ (X0 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X3)) := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : ((X4 ◇ (X1 ◇ X3)) ◇ (X4 ◇ X5)) = (X0 ◇ (X1 ◇ X3)) := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ X5) ◇ X5)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X5 := superpose eq10 eq7
  have eq34 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X2 ◇ X3) ◇ X1) ◇ X4)) = X3 := superpose eq10 eq7
  have eq39 (X0 X4 X5 X6 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ (X4 ◇ X6)) = X0 := superpose eq7 eq9
  have eq66 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X3 := superpose eq39 eq13
  have eq71 (X1 X2 X3 X4 X5 : G) : (((X3 ◇ X1) ◇ ((X4 ◇ X5) ◇ X5)) ◇ X2) = X5 := superpose eq66 eq29
  have eq84 (X2 X5 : G) : (X5 ◇ X2) = X5 := superpose eq66 eq71
  have eq86 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X1) ◇ X4)) = X3 := superpose eq84 eq34
  have eq99 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) = X3 := superpose eq84 eq86
  have eq100 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X3 := superpose eq84 eq99
  have eq101 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = X3 := superpose eq84 eq100
  have eq102 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq84 eq101
  have eq103 (X0 X3 : G) : X0 = X3 := superpose eq102 eq102
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq103 eq8
  subsumption eq108 eq103


@[equational_result]
theorem Equation26258_implies_Equation2 (G : Type*) [Magma G] (h : Equation26258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ (X0 ◇ (X3 ◇ X3))) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X0)) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0)))) := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X1) = (X0 ◇ ((X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))))) := superpose eq7 eq9
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq98 eq33


@[equational_result]
theorem Equation26259_implies_Equation2 (G : Type*) [Magma G] (h : Equation26259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation26261_implies_Equation2 (G : Type*) [Magma G] (h : Equation26261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) = X1 := superpose eq7 eq7
  have eq52 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq11
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq52
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq119 eq65


@[equational_result]
theorem Equation26262_implies_Equation2 (G : Type*) [Magma G] (h : Equation26262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation26263_implies_Equation2 (G : Type*) [Magma G] (h : Equation26263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq10 eq10
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq95 eq36


@[equational_result]
theorem Equation26264_implies_Equation2 (G : Type*) [Magma G] (h : Equation26264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26270_implies_Equation2 (G : Type*) [Magma G] (h : Equation26270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq154 eq53


@[equational_result]
theorem Equation26272_implies_Equation2 (G : Type*) [Magma G] (h : Equation26272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X2 ◇ X4) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X5)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq80 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq174 eq80


@[equational_result]
theorem Equation26276_implies_Equation2 (G : Type*) [Magma G] (h : Equation26276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation26278_implies_Equation2 (G : Type*) [Magma G] (h : Equation26278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X2) = ((X1 ◇ (X0 ◇ X1)) ◇ (X5 ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq163 eq59


@[equational_result]
theorem Equation26279_implies_Equation2 (G : Type*) [Magma G] (h : Equation26279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X1)) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq11
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq155 eq44


@[equational_result]
theorem Equation26280_implies_Equation2 (G : Type*) [Magma G] (h : Equation26280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X4 ◇ X4) = ((X1 ◇ (X0 ◇ X1)) ◇ (X5 ◇ X5)) := superpose eq7 eq7
  have eq48 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq68 (X0 X2 : G) : X0 = X2 := superpose eq48 eq48
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq173 eq68


@[equational_result]
theorem Equation26281_implies_Equation2 (G : Type*) [Magma G] (h : Equation26281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26289_implies_Equation2 (G : Type*) [Magma G] (h : Equation26289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq10
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq150 eq42


@[equational_result]
theorem Equation26292_implies_Equation2 (G : Type*) [Magma G] (h : Equation26292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) ◇ X1) = X0 := superpose eq7 eq10
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = X2 := superpose eq15 eq7
  have eq104 (X0 X3 : G) : X0 = X3 := superpose eq7 eq51
  have eq205 (X0 : G) : sK0 ≠ X0 := superpose eq104 eq8
  subsumption eq205 eq104


@[equational_result]
theorem Equation26293_implies_Equation2 (G : Type*) [Magma G] (h : Equation26293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq72 eq16


@[equational_result]
theorem Equation26295_implies_Equation2 (G : Type*) [Magma G] (h : Equation26295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2)))) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation26296_implies_Equation2 (G : Type*) [Magma G] (h : Equation26296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq72 eq16


@[equational_result]
theorem Equation26297_implies_Equation2 (G : Type*) [Magma G] (h : Equation26297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq11
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq163 eq55


@[equational_result]
theorem Equation26298_implies_Equation2 (G : Type*) [Magma G] (h : Equation26298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26305_implies_Equation2 (G : Type*) [Magma G] (h : Equation26305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X2 ◇ X2) = ((X1 ◇ (X0 ◇ X5)) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq89 (X0 X3 : G) : X0 = X3 := superpose eq7 eq25
  have eq194 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq194 eq89


@[equational_result]
theorem Equation26306_implies_Equation2 (G : Type*) [Magma G] (h : Equation26306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (((X1 ◇ X2) ◇ X4) ◇ X5)) ◇ X0) = X4 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) = X0 := superpose eq7 eq10
  have eq40 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq25 eq12
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq40 eq40
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation26307_implies_Equation2 (G : Type*) [Magma G] (h : Equation26307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X2 ◇ X4) = ((X1 ◇ (X0 ◇ X5)) ◇ (X1 ◇ X5)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq88 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq182 eq88


@[equational_result]
theorem Equation26308_implies_Equation2 (G : Type*) [Magma G] (h : Equation26308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 X6 X7 : G) : (X2 ◇ X5) = ((X1 ◇ (X0 ◇ X6)) ◇ (X1 ◇ X7)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq83 (X0 X5 : G) : X0 = X5 := superpose eq7 eq25
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq177 eq83


@[equational_result]
theorem Equation26310_implies_Equation2 (G : Type*) [Magma G] (h : Equation26310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (((X2 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X4) ◇ X5)) ◇ X0) = X4 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) = X0 := superpose eq7 eq10
  have eq38 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X5)) ◇ X0) = X4 := superpose eq25 eq12
  have eq55 (X0 X5 : G) : X0 = X5 := superpose eq38 eq38
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq80 eq55


@[equational_result]
theorem Equation26311_implies_Equation2 (G : Type*) [Magma G] (h : Equation26311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq65 eq14


@[equational_result]
theorem Equation26312_implies_Equation2 (G : Type*) [Magma G] (h : Equation26312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation26313_implies_Equation2 (G : Type*) [Magma G] (h : Equation26313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X6 : G) : (X0 ◇ (X2 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation26315_implies_Equation2 (G : Type*) [Magma G] (h : Equation26315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X2) = ((X1 ◇ (X0 ◇ X5)) ◇ (X5 ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq88 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq183 eq88


@[equational_result]
theorem Equation26316_implies_Equation2 (G : Type*) [Magma G] (h : Equation26316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation26317_implies_Equation2 (G : Type*) [Magma G] (h : Equation26317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = ((X1 ◇ X0) ◇ ((X4 ◇ X4) ◇ (X4 ◇ X4))) := superpose eq7 eq7
  have eq11 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X3 ◇ X4))) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = X4 := superpose eq11 eq10
  have eq14 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ (X3 ◇ X3)) = X0 := superpose eq12 eq7
  have eq16 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq12 eq12
  have eq17 (X0 X3 : G) : (X3 ◇ (X3 ◇ X3)) = X0 := superpose eq16 eq14
  have eq21 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq16 eq17
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation26318_implies_Equation2 (G : Type*) [Magma G] (h : Equation26318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation26320_implies_Equation2 (G : Type*) [Magma G] (h : Equation26320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 X6 X7 : G) : (X5 ◇ X2) = ((X1 ◇ (X0 ◇ X6)) ◇ (X7 ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq83 (X0 X5 : G) : X0 = X5 := superpose eq7 eq25
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq191 eq83


@[equational_result]
theorem Equation26321_implies_Equation2 (G : Type*) [Magma G] (h : Equation26321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X6 ◇ X4)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation26322_implies_Equation2 (G : Type*) [Magma G] (h : Equation26322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X6 ◇ X3)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation26323_implies_Equation2 (G : Type*) [Magma G] (h : Equation26323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X6 ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26324_implies_Equation2 (G : Type*) [Magma G] (h : Equation26324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X5 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26326_implies_Equation2 (G : Type*) [Magma G] (h : Equation26326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X3 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X3 ◇ X1) ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq9
  have eq32 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq46 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq14 eq9
  have eq90 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq14 eq46
  have eq97 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq46 eq9
  have eq101 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq46 eq14
  have eq128 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq16
  have eq155 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq128 eq101
  have eq160 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) ◇ X0) = X0 := superpose eq97 eq7
  have eq236 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq155 eq9
  have eq243 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq155 eq9
  have eq261 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq236 eq243
  have eq269 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq261 eq97
  have eq272 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) = X0 := superpose eq261 eq160
  have eq289 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq261 eq269
  have eq290 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq289 eq261
  have eq301 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose eq290 eq32
  have eq304 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq290 eq128
  have eq308 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose eq290 eq272
  have eq309 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq290 eq308
  have eq310 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ X0) := superpose eq309 eq90
  have eq311 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq290 eq310
  have eq327 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose eq311 eq301
  have eq352 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq311 eq327
  have eq353 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq290 eq352
  have eq424 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) := superpose eq353 eq46
  have eq437 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq311 eq424
  have eq438 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq290 eq437
  have eq439 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq290 eq438
  have eq585 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq439
  have eq631 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq585 eq46
  have eq753 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq439 eq631
  have eq1060 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq585 eq753
  have eq1102 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1060 eq304
  have eq1157 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X1)) = (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1)))) ◇ X0) := superpose eq1102 eq11
  have eq1407 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X3 ◇ X1)) := superpose eq1102 eq1157
  have eq1408 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq1102 eq1407
  have eq1409 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq1102 eq1408
  have eq1420 (X0 X2 : G) : X0 = X2 := superpose eq1409 eq1409
  have eq1425 (X0 : G) : sK0 ≠ X0 := superpose eq1420 eq8
  subsumption eq1425 eq1420


@[equational_result]
theorem Equation26328_implies_Equation2 (G : Type*) [Magma G] (h : Equation26328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X4)) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X3) ◇ X0)) = ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq9
  have eq26 (X0 X1 X3 X4 : G) : (X3 ◇ ((X4 ◇ X3) ◇ X0)) = ((X1 ◇ X3) ◇ X0) := superpose eq16 eq11
  have eq33 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ X2) ◇ X4) = (X2 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4)) := superpose eq26 eq26
  have eq34 (X0 X1 X2 X4 : G) : ((X4 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq26 eq26
  have eq42 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ X2) ◇ X4) = (X2 ◇ ((X1 ◇ X0) ◇ X4)) := superpose eq16 eq33
  have eq43 (X0 X2 X4 : G) : ((X4 ◇ X0) ◇ X2) = X0 := superpose eq16 eq34
  have eq48 (X0 X1 X2 X4 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X4)) = X2 := superpose eq43 eq42
  have eq51 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq43 eq48
  have eq52 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq51 eq16
  have eq56 (X0 X1 : G) : X0 = X1 := superpose eq51 eq52
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq69 eq56


@[equational_result]
theorem Equation26330_implies_Equation2 (G : Type*) [Magma G] (h : Equation26330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq26 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq10
  have eq31 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq13 eq22
  have eq33 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X2) := superpose eq31 eq10
  have eq42 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X2) = X2 := superpose eq26 eq33
  have eq54 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X2 := superpose eq42 eq42
  have eq57 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq26 eq54
  have eq61 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq57 eq31
  have eq68 (X0 X2 : G) : X0 = X2 := superpose eq61 eq61
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq76 eq68


@[equational_result]
theorem Equation26332_implies_Equation2 (G : Type*) [Magma G] (h : Equation26332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X4)) ◇ ((X1 ◇ X2) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X4)) := superpose eq7 eq7
  have eq40 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq10
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq40
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq146 eq61


@[equational_result]
theorem Equation26334_implies_Equation2 (G : Type*) [Magma G] (h : Equation26334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq10
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq83 eq30


@[equational_result]
theorem Equation26336_implies_Equation2 (G : Type*) [Magma G] (h : Equation26336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X2 ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X1) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 X5 X6 : G) : (((((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X4) ◇ X5) ◇ X5) ◇ (X4 ◇ X6)) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq10 eq10
  have eq52 (X0 X1 X2 X3 X6 X7 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X1 ◇ X3)) ◇ X6) = X7 := superpose eq10 eq11
  have eq62 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X4) = X0 := superpose eq7 eq26
  have eq112 (X0 X4 X5 X6 : G) : (((X0 ◇ X5) ◇ X5) ◇ (X4 ◇ X6)) = X0 := superpose eq62 eq12
  have eq126 (X0 X1 X6 X7 : G) : ((X0 ◇ X1) ◇ X6) = X7 := superpose eq112 eq52
  have eq138 (X0 X4 : G) : X0 = X4 := superpose eq7 eq126
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq138 eq8
  subsumption eq171 eq138


@[equational_result]
theorem Equation26338_implies_Equation2 (G : Type*) [Magma G] (h : Equation26338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0)))) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq121 eq45


@[equational_result]
theorem Equation26339_implies_Equation2 (G : Type*) [Magma G] (h : Equation26339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation26340_implies_Equation2 (G : Type*) [Magma G] (h : Equation26340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X4)) ◇ (X5 ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq36 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq10
  have eq51 (X0 X1 : G) : X0 = X1 := superpose eq9 eq36
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq153 eq51


@[equational_result]
theorem Equation26341_implies_Equation2 (G : Type*) [Magma G] (h : Equation26341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26343_implies_Equation2 (G : Type*) [Magma G] (h : Equation26343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X3 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq9
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) = ((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq9 eq10
  have eq41 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq14
  have eq79 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq9 eq11
  have eq84 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq11 eq7
  have eq114 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq41 eq41
  have eq118 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) := superpose eq9 eq41
  have eq119 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) ◇ X0) := superpose eq10 eq41
  have eq121 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) := superpose eq41 eq41
  have eq136 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X0) := superpose eq121 eq79
  have eq138 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) = ((X1 ◇ X2) ◇ X1) := superpose eq121 eq27
  have eq152 (X0 X1 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq136 eq84
  have eq222 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) = X2 := superpose eq152 eq114
  have eq223 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) = X3 := superpose eq7 eq114
  have eq227 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) = X3 := superpose eq41 eq114
  have eq336 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq222 eq222
  have eq341 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1))) = X2 := superpose eq152 eq222
  have eq364 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq222 eq41
  have eq465 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq336 eq138
  have eq495 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0)))) = X3 := superpose eq465 eq223
  have eq538 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq465 eq495
  have eq539 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) = X1 := superpose eq538 eq118
  have eq541 (X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq539 eq119
  have eq542 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X1 := superpose eq539 eq121
  have eq588 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq542 eq227
  have eq598 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq542 eq341
  have eq638 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq598 eq364
  have eq641 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq638 eq541
  have eq659 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X0)) = X3 := superpose eq641 eq588
  have eq677 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X3 := superpose eq641 eq659
  have eq678 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq641 eq677
  have eq685 (X0 X1 : G) : X0 = X1 := superpose eq641 eq678
  have eq695 (X0 : G) : sK0 ≠ X0 := superpose eq685 eq8
  subsumption eq695 eq685


@[equational_result]
theorem Equation26345_implies_Equation2 (G : Type*) [Magma G] (h : Equation26345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq9
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq17
  have eq86 (X0 X3 : G) : X0 = X3 := superpose eq17 eq49
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq170 eq86


@[equational_result]
theorem Equation26347_implies_Equation2 (G : Type*) [Magma G] (h : Equation26347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26348_implies_Equation2 (G : Type*) [Magma G] (h : Equation26348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26349_implies_Equation2 (G : Type*) [Magma G] (h : Equation26349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26351_implies_Equation2 (G : Type*) [Magma G] (h : Equation26351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation26352_implies_Equation2 (G : Type*) [Magma G] (h : Equation26352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26353_implies_Equation2 (G : Type*) [Magma G] (h : Equation26353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26355_implies_Equation2 (G : Type*) [Magma G] (h : Equation26355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26356_implies_Equation2 (G : Type*) [Magma G] (h : Equation26356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26357_implies_Equation2 (G : Type*) [Magma G] (h : Equation26357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26358_implies_Equation2 (G : Type*) [Magma G] (h : Equation26358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26362_implies_Equation2 (G : Type*) [Magma G] (h : Equation26362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq34 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq78 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq34 eq34
  have eq97 (X0 X3 : G) : X0 = X3 := superpose eq34 eq78
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq153 eq97


@[equational_result]
theorem Equation26364_implies_Equation2 (G : Type*) [Magma G] (h : Equation26364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26365_implies_Equation2 (G : Type*) [Magma G] (h : Equation26365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26366_implies_Equation2 (G : Type*) [Magma G] (h : Equation26366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26368_implies_Equation2 (G : Type*) [Magma G] (h : Equation26368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation26369_implies_Equation2 (G : Type*) [Magma G] (h : Equation26369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26370_implies_Equation2 (G : Type*) [Magma G] (h : Equation26370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26372_implies_Equation2 (G : Type*) [Magma G] (h : Equation26372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26373_implies_Equation2 (G : Type*) [Magma G] (h : Equation26373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26374_implies_Equation2 (G : Type*) [Magma G] (h : Equation26374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26375_implies_Equation2 (G : Type*) [Magma G] (h : Equation26375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26377_implies_Equation2 (G : Type*) [Magma G] (h : Equation26377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X4 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq31 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq10
  have eq45 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3)))) = X4 := superpose eq7 eq31
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq31 eq31
  have eq65 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq48 eq45
  have eq144 (X0 X4 : G) : X0 = X4 := superpose eq7 eq65
  have eq256 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq256 eq144


@[equational_result]
theorem Equation26378_implies_Equation2 (G : Type*) [Magma G] (h : Equation26378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X4 ◇ X2)) = X4 := superpose eq7 eq7
  have eq17 (X0 X3 X5 : G) : (X0 ◇ (X5 ◇ X3)) = X5 := superpose eq10 eq10
  have eq63 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq17
  have eq100 (X0 X5 : G) : X0 = X5 := superpose eq10 eq63
  have eq200 (X0 : G) : sK0 ≠ X0 := superpose eq100 eq8
  subsumption eq200 eq100


@[equational_result]
theorem Equation26379_implies_Equation2 (G : Type*) [Magma G] (h : Equation26379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X4)) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X0) = X4 := superpose eq17 eq10
  have eq42 (X0 X5 : G) : X0 = X5 := superpose eq33 eq33
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq44 eq42


@[equational_result]
theorem Equation26380_implies_Equation2 (G : Type*) [Magma G] (h : Equation26380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 X6 X7 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X5)) ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X5 X6 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq17 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq9
  have eq37 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq17
  have eq76 (X0 X6 : G) : X0 = X6 := superpose eq10 eq37
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq162 eq76


@[equational_result]
theorem Equation26382_implies_Equation2 (G : Type*) [Magma G] (h : Equation26382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26383_implies_Equation2 (G : Type*) [Magma G] (h : Equation26383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26384_implies_Equation2 (G : Type*) [Magma G] (h : Equation26384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26385_implies_Equation2 (G : Type*) [Magma G] (h : Equation26385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26387_implies_Equation2 (G : Type*) [Magma G] (h : Equation26387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26388_implies_Equation2 (G : Type*) [Magma G] (h : Equation26388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26389_implies_Equation2 (G : Type*) [Magma G] (h : Equation26389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26390_implies_Equation2 (G : Type*) [Magma G] (h : Equation26390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26392_implies_Equation2 (G : Type*) [Magma G] (h : Equation26392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26393_implies_Equation2 (G : Type*) [Magma G] (h : Equation26393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26394_implies_Equation2 (G : Type*) [Magma G] (h : Equation26394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26395_implies_Equation2 (G : Type*) [Magma G] (h : Equation26395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26397_implies_Equation2 (G : Type*) [Magma G] (h : Equation26397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26398_implies_Equation2 (G : Type*) [Magma G] (h : Equation26398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26399_implies_Equation2 (G : Type*) [Magma G] (h : Equation26399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26400_implies_Equation2 (G : Type*) [Magma G] (h : Equation26400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26401_implies_Equation2 (G : Type*) [Magma G] (h : Equation26401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26404_implies_Equation2 (G : Type*) [Magma G] (h : Equation26404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq10 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq14 eq13
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq19 eq9
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq20 eq20
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq20
  have eq34 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq20 eq26
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X1 ◇ X0)) := superpose eq34 eq19
  have eq38 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq35 eq17
  have eq45 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X1 := superpose eq29 eq35
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq29 eq38
  have eq49 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq45 eq47
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq49 eq49
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq60 eq55


@[equational_result]
theorem Equation26405_implies_Equation2 (G : Type*) [Magma G] (h : Equation26405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X0 ◇ X3) = ((X1 ◇ X0) ◇ ((X0 ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq11
  have eq30 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq10 eq10
  have eq35 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq14 eq30
  have eq37 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = X3 := superpose eq35 eq11
  have eq44 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq35 eq37
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq44 eq44
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq57 eq45


@[equational_result]
theorem Equation26407_implies_Equation2 (G : Type*) [Magma G] (h : Equation26407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)))) := superpose eq7 eq7
  have eq43 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0))) = X0 := superpose eq7 eq10
  have eq69 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq43 eq11
  have eq70 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq7 eq69
  have eq157 (X0 X2 : G) : X0 = X2 := superpose eq7 eq70
  have eq292 (X0 : G) : sK0 ≠ X0 := superpose eq157 eq8
  subsumption eq292 eq157


@[equational_result]
theorem Equation26408_implies_Equation2 (G : Type*) [Magma G] (h : Equation26408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (((((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) ◇ X3)) ◇ X0) = X3 := superpose eq10 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) ◇ X0) = X3 := superpose eq12 eq16
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ X2))))) = X1 := superpose eq9 eq10
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X2)) = X1 := superpose eq9 eq10
  have eq92 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ X2))))) ◇ X1) = X3 := superpose eq9 eq18
  have eq93 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) = X2 := superpose eq11 eq18
  have eq114 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq31 eq92
  have eq117 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X1 ◇ X2)) = X1 := superpose eq93 eq35
  have eq178 (X0 X2 : G) : X0 = X2 := superpose eq117 eq114
  have eq300 (X0 : G) : sK0 ≠ X0 := superpose eq178 eq8
  subsumption eq300 eq178


@[equational_result]
theorem Equation26409_implies_Equation2 (G : Type*) [Magma G] (h : Equation26409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ X0) ◇ X3) = ((X1 ◇ X0) ◇ (X1 ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq43 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) = X0 := superpose eq7 eq10
  have eq65 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq43 eq11
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq7 eq65
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq155 eq67


@[equational_result]
theorem Equation26412_implies_Equation2 (G : Type*) [Magma G] (h : Equation26412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq52 eq30


@[equational_result]
theorem Equation26413_implies_Equation2 (G : Type*) [Magma G] (h : Equation26413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq69 eq16


@[equational_result]
theorem Equation26415_implies_Equation2 (G : Type*) [Magma G] (h : Equation26415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X1 := superpose eq7 eq7
  have eq31 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq11
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq31
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq112 eq40


@[equational_result]
theorem Equation26416_implies_Equation2 (G : Type*) [Magma G] (h : Equation26416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq65 eq15


@[equational_result]
theorem Equation26417_implies_Equation2 (G : Type*) [Magma G] (h : Equation26417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X3 ◇ X3) = (X0 ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq141 eq53


@[equational_result]
theorem Equation26418_implies_Equation2 (G : Type*) [Magma G] (h : Equation26418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26422_implies_Equation2 (G : Type*) [Magma G] (h : Equation26422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq10
  have eq47 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq92 (X0 X3 : G) : X0 = X3 := superpose eq10 eq47
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq176 eq92


@[equational_result]
theorem Equation26424_implies_Equation2 (G : Type*) [Magma G] (h : Equation26424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation26425_implies_Equation2 (G : Type*) [Magma G] (h : Equation26425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26426_implies_Equation2 (G : Type*) [Magma G] (h : Equation26426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26428_implies_Equation2 (G : Type*) [Magma G] (h : Equation26428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26429_implies_Equation2 (G : Type*) [Magma G] (h : Equation26429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation26430_implies_Equation2 (G : Type*) [Magma G] (h : Equation26430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26432_implies_Equation2 (G : Type*) [Magma G] (h : Equation26432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26433_implies_Equation2 (G : Type*) [Magma G] (h : Equation26433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26434_implies_Equation2 (G : Type*) [Magma G] (h : Equation26434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation26435_implies_Equation2 (G : Type*) [Magma G] (h : Equation26435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26438_implies_Equation2 (G : Type*) [Magma G] (h : Equation26438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq10 eq10
  have eq18 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq14 eq13
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X2 := superpose eq18 eq9
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq35 eq29


@[equational_result]
theorem Equation26439_implies_Equation2 (G : Type*) [Magma G] (h : Equation26439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq11
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq98 (X0 X3 : G) : X0 = X3 := superpose eq11 eq50
  have eq189 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq189 eq98


@[equational_result]
theorem Equation26441_implies_Equation2 (G : Type*) [Magma G] (h : Equation26441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26442_implies_Equation2 (G : Type*) [Magma G] (h : Equation26442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26443_implies_Equation2 (G : Type*) [Magma G] (h : Equation26443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26445_implies_Equation2 (G : Type*) [Magma G] (h : Equation26445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26446_implies_Equation2 (G : Type*) [Magma G] (h : Equation26446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation26447_implies_Equation2 (G : Type*) [Magma G] (h : Equation26447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26449_implies_Equation2 (G : Type*) [Magma G] (h : Equation26449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26450_implies_Equation2 (G : Type*) [Magma G] (h : Equation26450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26451_implies_Equation2 (G : Type*) [Magma G] (h : Equation26451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26452_implies_Equation2 (G : Type*) [Magma G] (h : Equation26452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26454_implies_Equation2 (G : Type*) [Magma G] (h : Equation26454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3)))) = X4 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq10 eq10
  have eq21 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq14 eq13
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq153 eq44


@[equational_result]
theorem Equation26455_implies_Equation2 (G : Type*) [Magma G] (h : Equation26455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ ((X2 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq10 (X0 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq10 eq10
  have eq19 (X1 X2 X3 : G) : (X1 ◇ X1) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq14 eq13
  have eq21 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = X4 := superpose eq19 eq9
  have eq33 (X0 X1 : G) : X0 = X1 := superpose eq10 eq21
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq42 eq33


@[equational_result]
theorem Equation26456_implies_Equation2 (G : Type*) [Magma G] (h : Equation26456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq21 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X0) = X4 := superpose eq13 eq9
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq10 eq21
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq34 eq26


@[equational_result]
theorem Equation26457_implies_Equation2 (G : Type*) [Magma G] (h : Equation26457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : ((X1 ◇ X0) ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq10
  have eq47 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq96 (X0 X4 : G) : X0 = X4 := superpose eq10 eq47
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq188 eq96


@[equational_result]
theorem Equation26459_implies_Equation2 (G : Type*) [Magma G] (h : Equation26459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26460_implies_Equation2 (G : Type*) [Magma G] (h : Equation26460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26461_implies_Equation2 (G : Type*) [Magma G] (h : Equation26461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26462_implies_Equation2 (G : Type*) [Magma G] (h : Equation26462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26464_implies_Equation2 (G : Type*) [Magma G] (h : Equation26464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26465_implies_Equation2 (G : Type*) [Magma G] (h : Equation26465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26466_implies_Equation2 (G : Type*) [Magma G] (h : Equation26466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26467_implies_Equation2 (G : Type*) [Magma G] (h : Equation26467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26469_implies_Equation2 (G : Type*) [Magma G] (h : Equation26469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26470_implies_Equation2 (G : Type*) [Magma G] (h : Equation26470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26471_implies_Equation2 (G : Type*) [Magma G] (h : Equation26471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26472_implies_Equation2 (G : Type*) [Magma G] (h : Equation26472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26474_implies_Equation2 (G : Type*) [Magma G] (h : Equation26474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26475_implies_Equation2 (G : Type*) [Magma G] (h : Equation26475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26476_implies_Equation2 (G : Type*) [Magma G] (h : Equation26476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26477_implies_Equation2 (G : Type*) [Magma G] (h : Equation26477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26478_implies_Equation2 (G : Type*) [Magma G] (h : Equation26478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26480_implies_Equation2 (G : Type*) [Magma G] (h : Equation26480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ (X5 ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X1))))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq9 eq9
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) ◇ X0) := superpose eq9 eq9
  have eq30 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq9 eq10
  have eq48 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq16 eq16
  have eq59 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := superpose eq48 eq30
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1)))) = X2 := superpose eq59 eq11
  have eq67 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ (X1 ◇ (X3 ◇ X0))) ◇ X0) := superpose eq59 eq18
  have eq84 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) = X2 := superpose eq59 eq64
  have eq85 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq59 eq84
  have eq92 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ X0) := superpose eq59 eq67
  have eq93 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq59 eq92
  have eq94 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X0 := superpose eq48 eq93
  have eq95 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq94 eq59
  have eq100 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq95 eq85
  have eq103 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq95 eq100
  have eq130 (X0 X2 : G) : X0 = X2 := superpose eq103 eq103
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq130 eq8
  subsumption eq132 eq130


@[equational_result]
theorem Equation26481_implies_Equation2 (G : Type*) [Magma G] (h : Equation26481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0)))) = X4 := superpose eq7 eq11
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq11 eq11
  have eq22 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq14 eq13
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq129 eq39


@[equational_result]
theorem Equation26482_implies_Equation2 (G : Type*) [Magma G] (h : Equation26482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ (X5 ◇ (X0 ◇ X4))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq11
  have eq42 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq13 eq13
  have eq71 (X0 X1 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X0) = X5 := superpose eq42 eq9
  have eq80 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq42 eq71
  have eq92 (X0 X2 : G) : X0 = X2 := superpose eq80 eq80
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq94 eq92


@[equational_result]
theorem Equation26483_implies_Equation2 (G : Type*) [Magma G] (h : Equation26483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 X6 : G) : ((X0 ◇ X1) ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq14
  have eq83 (X0 X4 : G) : X0 = X4 := superpose eq11 eq34
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq175 eq83


@[equational_result]
theorem Equation26485_implies_Equation2 (G : Type*) [Magma G] (h : Equation26485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq35
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq137 eq57


@[equational_result]
theorem Equation26486_implies_Equation2 (G : Type*) [Magma G] (h : Equation26486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq155 eq60


@[equational_result]
theorem Equation26487_implies_Equation2 (G : Type*) [Magma G] (h : Equation26487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ (X1 ◇ (X2 ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X1 ◇ X0) ◇ (X1 ◇ ((X3 ◇ X4) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X2)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq9
  have eq20 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X0) = X4 := superpose eq9 eq9
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = ((X4 ◇ (X5 ◇ X3)) ◇ (X4 ◇ X0)) := superpose eq7 eq10
  have eq67 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq17 eq37
  have eq68 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X4 := superpose eq67 eq11
  have eq78 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq68 eq20
  have eq83 (X0 X3 : G) : X0 = X3 := superpose eq78 eq78
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq91 eq83


@[equational_result]
theorem Equation26488_implies_Equation2 (G : Type*) [Magma G] (h : Equation26488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X2 ◇ X5) = ((X1 ◇ X0) ◇ (X1 ◇ X6)) := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq35
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq159 eq57


@[equational_result]
theorem Equation26490_implies_Equation2 (G : Type*) [Magma G] (h : Equation26490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq156 eq61


@[equational_result]
theorem Equation26491_implies_Equation2 (G : Type*) [Magma G] (h : Equation26491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq154 eq59


@[equational_result]
theorem Equation26492_implies_Equation2 (G : Type*) [Magma G] (h : Equation26492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X3)) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq41 eq15


@[equational_result]
theorem Equation26493_implies_Equation2 (G : Type*) [Magma G] (h : Equation26493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 X6 : G) : (X0 ◇ (X2 ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation26495_implies_Equation2 (G : Type*) [Magma G] (h : Equation26495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ ((X4 ◇ X2) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X0) ◇ (((X3 ◇ X4) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq10
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq45
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq155 eq68


@[equational_result]
theorem Equation26496_implies_Equation2 (G : Type*) [Magma G] (h : Equation26496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation26497_implies_Equation2 (G : Type*) [Magma G] (h : Equation26497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X3 ◇ X4) = (X0 ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq120 eq49


@[equational_result]
theorem Equation26498_implies_Equation2 (G : Type*) [Magma G] (h : Equation26498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation26500_implies_Equation2 (G : Type*) [Magma G] (h : Equation26500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X5 ◇ X2) = ((X1 ◇ X0) ◇ (X6 ◇ X1)) := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq35
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq131 eq57


@[equational_result]
theorem Equation26501_implies_Equation2 (G : Type*) [Magma G] (h : Equation26501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 X6 : G) : (X0 ◇ (X6 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation26502_implies_Equation2 (G : Type*) [Magma G] (h : Equation26502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X6 ◇ X5)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation26503_implies_Equation2 (G : Type*) [Magma G] (h : Equation26503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X4 ◇ X5) = (X0 ◇ (X6 ◇ X6)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq141 eq53


@[equational_result]
theorem Equation26504_implies_Equation2 (G : Type*) [Magma G] (h : Equation26504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X6 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26506_implies_Equation2 (G : Type*) [Magma G] (h : Equation26506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X5 ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X4 ◇ (X0 ◇ X1))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X4 ◇ X5) ◇ X1)) = (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq10
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose eq10 eq20
  have eq83 (X0 X1 X2 X3 X4 X7 : G) : ((X4 ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X0)) ◇ (X7 ◇ X4)) = X7 := superpose eq11 eq20
  have eq85 (X0 X1 X2 X3 X4 X5 : G) : ((((X4 ◇ X5) ◇ X1) ◇ (X4 ◇ X5)) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X0)) = X1 := superpose eq11 eq10
  have eq88 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X4 ◇ X5) ◇ X1) ◇ ((X6 ◇ X7) ◇ ((X4 ◇ X5) ◇ X1))) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X0)) = X1 := superpose eq11 eq7
  have eq101 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X3 ◇ X0) ◇ ((X6 ◇ X7) ◇ (X3 ◇ X0))) = ((X3 ◇ (X4 ◇ (X5 ◇ X4))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq11 eq20
  have eq119 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X0)) = X1 := superpose eq11 eq37
  have eq140 (X1 X4 X7 : G) : (X1 ◇ (X7 ◇ X4)) = X7 := superpose eq119 eq83
  have eq143 (X0 X3 X6 X7 : G) : ((X3 ◇ X0) ◇ ((X6 ◇ X7) ◇ (X3 ◇ X0))) = X0 := superpose eq140 eq101
  have eq157 (X0 X1 X2 X3 X4 X5 : G) : ((((X4 ◇ X5) ◇ X1) ◇ (X4 ◇ X5)) ◇ ((X2 ◇ X3) ◇ X0)) = X1 := superpose eq140 eq85
  have eq158 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X4 ◇ X5) ◇ X1) ◇ ((X6 ◇ X7) ◇ ((X4 ◇ X5) ◇ X1))) ◇ ((X2 ◇ X3) ◇ X0)) = X1 := superpose eq140 eq88
  have eq195 (X0 X3 : G) : ((X3 ◇ X0) ◇ X3) = X0 := superpose eq140 eq143
  have eq196 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = (X1 ◇ X0) := superpose eq195 eq22
  have eq204 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X1 := superpose eq195 eq157
  have eq206 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq204 eq196
  have eq215 (X1 X2 X3 X4 X5 X6 X7 : G) : ((((X4 ◇ X5) ◇ X1) ◇ ((X6 ◇ X7) ◇ ((X4 ◇ X5) ◇ X1))) ◇ (X2 ◇ X3)) = X1 := superpose eq206 eq158
  have eq216 (X1 X2 X4 X5 X6 X7 : G) : ((((X4 ◇ X5) ◇ X1) ◇ ((X6 ◇ X7) ◇ ((X4 ◇ X5) ◇ X1))) ◇ X2) = X1 := superpose eq206 eq215
  have eq217 (X1 X2 X4 X5 : G) : (((X4 ◇ X5) ◇ X1) ◇ X2) = X1 := superpose eq206 eq216
  have eq218 (X1 X2 X4 X5 : G) : ((X4 ◇ X5) ◇ X2) = X1 := superpose eq206 eq217
  have eq219 (X1 X2 X4 : G) : (X4 ◇ X2) = X1 := superpose eq206 eq218
  have eq220 (X0 X3 : G) : X0 = X3 := superpose eq219 eq219
  have eq239 (X0 : G) : sK0 ≠ X0 := superpose eq220 eq8
  subsumption eq239 eq220


@[equational_result]
theorem Equation26507_implies_Equation2 (G : Type*) [Magma G] (h : Equation26507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X4 ◇ X2)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X5) ◇ X4)) = ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq10 eq10
  have eq25 (X0 X2 X3 X4 X5 : G) : (X4 ◇ ((X2 ◇ X5) ◇ X4)) = (((X0 ◇ X2) ◇ X3) ◇ X0) := superpose eq14 eq11
  have eq33 (X0 X1 X2 X3 X5 X6 : G) : (((X5 ◇ (X3 ◇ X1)) ◇ X6) ◇ X5) = (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq25 eq25
  have eq52 (X1 X2 X3 X5 X6 : G) : (((X5 ◇ (X3 ◇ X1)) ◇ X6) ◇ X5) = (X3 ◇ (X1 ◇ X2)) := superpose eq14 eq33
  have eq53 (X1 X3 X5 X6 : G) : (((X5 ◇ (X3 ◇ X1)) ◇ X6) ◇ X5) = X1 := superpose eq14 eq52
  have eq54 (X1 X3 X5 X6 : G) : ((X3 ◇ X6) ◇ X5) = X1 := superpose eq14 eq53
  have eq66 (X0 X4 : G) : X0 = X4 := superpose eq10 eq54
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq82 eq66


@[equational_result]
theorem Equation26508_implies_Equation2 (G : Type*) [Magma G] (h : Equation26508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X5 ◇ (X0 ◇ X4))) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq9 eq9
  have eq50 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq14 eq14
  have eq81 (X0 X1 X5 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X5 := superpose eq50 eq9
  have eq94 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq50 eq81
  have eq98 (X0 X2 : G) : X0 = X2 := superpose eq94 eq94
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq100 eq98


@[equational_result]
theorem Equation26509_implies_Equation2 (G : Type*) [Magma G] (h : Equation26509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 X6 : G) : ((X0 ◇ X1) ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq82 (X0 X4 : G) : X0 = X4 := superpose eq11 eq34
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq174 eq82


@[equational_result]
theorem Equation26511_implies_Equation2 (G : Type*) [Magma G] (h : Equation26511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26512_implies_Equation2 (G : Type*) [Magma G] (h : Equation26512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26513_implies_Equation2 (G : Type*) [Magma G] (h : Equation26513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26514_implies_Equation2 (G : Type*) [Magma G] (h : Equation26514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26516_implies_Equation2 (G : Type*) [Magma G] (h : Equation26516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26517_implies_Equation2 (G : Type*) [Magma G] (h : Equation26517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26518_implies_Equation2 (G : Type*) [Magma G] (h : Equation26518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26519_implies_Equation2 (G : Type*) [Magma G] (h : Equation26519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26521_implies_Equation2 (G : Type*) [Magma G] (h : Equation26521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26522_implies_Equation2 (G : Type*) [Magma G] (h : Equation26522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26523_implies_Equation2 (G : Type*) [Magma G] (h : Equation26523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26524_implies_Equation2 (G : Type*) [Magma G] (h : Equation26524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26526_implies_Equation2 (G : Type*) [Magma G] (h : Equation26526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26527_implies_Equation2 (G : Type*) [Magma G] (h : Equation26527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26528_implies_Equation2 (G : Type*) [Magma G] (h : Equation26528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26529_implies_Equation2 (G : Type*) [Magma G] (h : Equation26529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26530_implies_Equation2 (G : Type*) [Magma G] (h : Equation26530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26532_implies_Equation2 (G : Type*) [Magma G] (h : Equation26532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3)))) ◇ (X5 ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2)))) = X4 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (X0 ◇ (X8 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X4 ◇ (X5 ◇ ((X6 ◇ X7) ◇ X6)))))) = X8 := superpose eq9 eq9
  have eq34 (X0 X1 X2 X5 : G) : (X0 ◇ (X5 ◇ (X1 ◇ X2))) = X5 := superpose eq10 eq9
  have eq45 (X0 X4 X8 : G) : (X0 ◇ (X8 ◇ X4)) = X8 := superpose eq34 eq33
  have eq58 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq45 eq34
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq58 eq58
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq83 eq59


@[equational_result]
theorem Equation26533_implies_Equation2 (G : Type*) [Magma G] (h : Equation26533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2)))) = X4 := superpose eq7 eq11
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq11 eq11
  have eq22 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq14 eq13
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq130 eq38


@[equational_result]
theorem Equation26534_implies_Equation2 (G : Type*) [Magma G] (h : Equation26534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ ((X3 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X2)) = X3 := superpose eq11 eq7
  have eq21 (X0 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ X6) ◇ X5))) = X4 := superpose eq7 eq10
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq7 eq10
  have eq40 (X0 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ X5)) = X0 := superpose eq17 eq30
  have eq41 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq40 eq21
  have eq47 (X0 X3 : G) : X0 = X3 := superpose eq11 eq41
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq69 eq47


@[equational_result]
theorem Equation26535_implies_Equation2 (G : Type*) [Magma G] (h : Equation26535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : ((X1 ◇ X0) ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq10
  have eq47 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq96 (X0 X4 : G) : X0 = X4 := superpose eq10 eq47
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq188 eq96


@[equational_result]
theorem Equation26537_implies_Equation2 (G : Type*) [Magma G] (h : Equation26537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26538_implies_Equation2 (G : Type*) [Magma G] (h : Equation26538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26539_implies_Equation2 (G : Type*) [Magma G] (h : Equation26539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26540_implies_Equation2 (G : Type*) [Magma G] (h : Equation26540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26542_implies_Equation2 (G : Type*) [Magma G] (h : Equation26542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26543_implies_Equation2 (G : Type*) [Magma G] (h : Equation26543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26544_implies_Equation2 (G : Type*) [Magma G] (h : Equation26544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26545_implies_Equation2 (G : Type*) [Magma G] (h : Equation26545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26547_implies_Equation2 (G : Type*) [Magma G] (h : Equation26547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26548_implies_Equation2 (G : Type*) [Magma G] (h : Equation26548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26549_implies_Equation2 (G : Type*) [Magma G] (h : Equation26549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26550_implies_Equation2 (G : Type*) [Magma G] (h : Equation26550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26552_implies_Equation2 (G : Type*) [Magma G] (h : Equation26552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26553_implies_Equation2 (G : Type*) [Magma G] (h : Equation26553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26554_implies_Equation2 (G : Type*) [Magma G] (h : Equation26554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26555_implies_Equation2 (G : Type*) [Magma G] (h : Equation26555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26556_implies_Equation2 (G : Type*) [Magma G] (h : Equation26556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26558_implies_Equation2 (G : Type*) [Magma G] (h : Equation26558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X5 ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ X1)) = X5 := superpose eq7 eq10
  have eq45 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq13 eq13
  have eq61 (X0 X1 X5 : G) : (X0 ◇ (X5 ◇ X1)) = X5 := superpose eq45 eq9
  have eq69 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq61 eq45
  have eq75 (X0 X3 : G) : X0 = X3 := superpose eq13 eq69
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq119 eq75


@[equational_result]
theorem Equation26559_implies_Equation2 (G : Type*) [Magma G] (h : Equation26559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3)))) = X4 := superpose eq7 eq11
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq11 eq11
  have eq21 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq14 eq13
  have eq37 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq139 eq37


@[equational_result]
theorem Equation26560_implies_Equation2 (G : Type*) [Magma G] (h : Equation26560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X1))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq11
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq13 eq13
  have eq69 (X0 X1 X2 X4 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X4 := superpose eq41 eq10
  have eq79 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X1)) = X4 := superpose eq41 eq69
  have eq88 (X0 X3 : G) : X0 = X3 := superpose eq79 eq79
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq96 eq88


@[equational_result]
theorem Equation26561_implies_Equation2 (G : Type*) [Magma G] (h : Equation26561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 X6 : G) : ((X0 ◇ X1) ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq97 (X0 X4 : G) : X0 = X4 := superpose eq11 eq48
  have eq189 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq189 eq97


@[equational_result]
theorem Equation26563_implies_Equation2 (G : Type*) [Magma G] (h : Equation26563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26564_implies_Equation2 (G : Type*) [Magma G] (h : Equation26564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26565_implies_Equation2 (G : Type*) [Magma G] (h : Equation26565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26566_implies_Equation2 (G : Type*) [Magma G] (h : Equation26566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26568_implies_Equation2 (G : Type*) [Magma G] (h : Equation26568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26569_implies_Equation2 (G : Type*) [Magma G] (h : Equation26569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26570_implies_Equation2 (G : Type*) [Magma G] (h : Equation26570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26571_implies_Equation2 (G : Type*) [Magma G] (h : Equation26571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26573_implies_Equation2 (G : Type*) [Magma G] (h : Equation26573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26574_implies_Equation2 (G : Type*) [Magma G] (h : Equation26574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26575_implies_Equation2 (G : Type*) [Magma G] (h : Equation26575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation26576_implies_Equation2 (G : Type*) [Magma G] (h : Equation26576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26578_implies_Equation2 (G : Type*) [Magma G] (h : Equation26578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26579_implies_Equation2 (G : Type*) [Magma G] (h : Equation26579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26580_implies_Equation2 (G : Type*) [Magma G] (h : Equation26580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26581_implies_Equation2 (G : Type*) [Magma G] (h : Equation26581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26582_implies_Equation2 (G : Type*) [Magma G] (h : Equation26582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26584_implies_Equation2 (G : Type*) [Magma G] (h : Equation26584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 : G) : ((X1 ◇ X0) ◇ (X6 ◇ X1)) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X5 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) = X5 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq10 eq10
  have eq21 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq14 eq13
  have eq38 (X0 X5 : G) : X0 = X5 := superpose eq7 eq21
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq143 eq38


@[equational_result]
theorem Equation26585_implies_Equation2 (G : Type*) [Magma G] (h : Equation26585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : ((X1 ◇ X0) ◇ (X6 ◇ X2)) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq10
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq103 (X0 X3 : G) : X0 = X3 := superpose eq50 eq50
  have eq198 (X0 : G) : sK0 ≠ X0 := superpose eq103 eq8
  subsumption eq198 eq103


@[equational_result]
theorem Equation26586_implies_Equation2 (G : Type*) [Magma G] (h : Equation26586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X6 X7 : G) : ((X1 ◇ (X0 ◇ X6)) ◇ (X7 ◇ (X0 ◇ X4))) = X7 := superpose eq7 eq7
  have eq11 (X0 X1 X6 : G) : ((X0 ◇ X1) ◇ (X6 ◇ X1)) = X6 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ (X5 ◇ (X0 ◇ X3))) = X5 := superpose eq7 eq11
  have eq42 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq13 eq13
  have eq62 (X0 X1 X6 X7 : G) : ((X1 ◇ (X0 ◇ X6)) ◇ X0) = X7 := superpose eq42 eq9
  have eq72 (X0 X7 : G) : (X0 ◇ X0) = X7 := superpose eq42 eq62
  have eq77 (X0 X2 : G) : X0 = X2 := superpose eq11 eq72
  have eq86 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq86 eq77


@[equational_result]
theorem Equation26587_implies_Equation2 (G : Type*) [Magma G] (h : Equation26587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : ((X1 ◇ X0) ◇ (X6 ◇ (X0 ◇ X5))) = X6 := superpose eq7 eq7
  have eq11 (X0 X1 X5 X6 : G) : ((X0 ◇ X1) ◇ (X6 ◇ X5)) = X6 := superpose eq7 eq7
  have eq14 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq23 (X0 X1 X6 : G) : ((X1 ◇ X0) ◇ X0) = X6 := superpose eq14 eq10
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation26588_implies_Equation2 (G : Type*) [Magma G] (h : Equation26588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X7 X8 : G) : ((X1 ◇ X0) ◇ (X7 ◇ X8)) = X7 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq10
  have eq47 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq96 (X0 X4 : G) : X0 = X4 := superpose eq10 eq47
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq188 eq96


@[equational_result]
theorem Equation26590_implies_Equation2 (G : Type*) [Magma G] (h : Equation26590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26591_implies_Equation2 (G : Type*) [Magma G] (h : Equation26591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26592_implies_Equation2 (G : Type*) [Magma G] (h : Equation26592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26593_implies_Equation2 (G : Type*) [Magma G] (h : Equation26593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26594_implies_Equation2 (G : Type*) [Magma G] (h : Equation26594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X1 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26596_implies_Equation2 (G : Type*) [Magma G] (h : Equation26596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26597_implies_Equation2 (G : Type*) [Magma G] (h : Equation26597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26598_implies_Equation2 (G : Type*) [Magma G] (h : Equation26598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26599_implies_Equation2 (G : Type*) [Magma G] (h : Equation26599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26600_implies_Equation2 (G : Type*) [Magma G] (h : Equation26600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X2 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26602_implies_Equation2 (G : Type*) [Magma G] (h : Equation26602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26603_implies_Equation2 (G : Type*) [Magma G] (h : Equation26603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26604_implies_Equation2 (G : Type*) [Magma G] (h : Equation26604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26605_implies_Equation2 (G : Type*) [Magma G] (h : Equation26605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26606_implies_Equation2 (G : Type*) [Magma G] (h : Equation26606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X3 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26608_implies_Equation2 (G : Type*) [Magma G] (h : Equation26608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26609_implies_Equation2 (G : Type*) [Magma G] (h : Equation26609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26610_implies_Equation2 (G : Type*) [Magma G] (h : Equation26610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26611_implies_Equation2 (G : Type*) [Magma G] (h : Equation26611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26612_implies_Equation2 (G : Type*) [Magma G] (h : Equation26612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26614_implies_Equation2 (G : Type*) [Magma G] (h : Equation26614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X5 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26615_implies_Equation2 (G : Type*) [Magma G] (h : Equation26615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X5 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26616_implies_Equation2 (G : Type*) [Magma G] (h : Equation26616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X5 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26617_implies_Equation2 (G : Type*) [Magma G] (h : Equation26617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X5 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26618_implies_Equation2 (G : Type*) [Magma G] (h : Equation26618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X5 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26619_implies_Equation2 (G : Type*) [Magma G] (h : Equation26619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X5 ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation26825_implies_Equation2 (G : Type*) [Magma G] (h : Equation26825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq9
  have eq17 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq11
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X2)) = ((((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2)))) ◇ X2) := superpose eq10 eq10
  have eq24 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) ◇ X1) := superpose eq10 eq10
  have eq29 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X2)) = (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X2) := superpose eq7 eq21
  have eq30 (X1 X3 : G) : (((X3 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) = X1 := superpose eq7 eq24
  have eq31 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X2)) = X2 := superpose eq30 eq29
  have eq32 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq31 eq30
  have eq38 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq32 eq9
  have eq39 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X2 := superpose eq32 eq31
  have eq41 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq17 eq38
  have eq64 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq32 eq41
  have eq66 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq17 eq64
  have eq68 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq66 eq39
  have eq71 (X0 X1 : G) : X0 = X1 := superpose eq68 eq66
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq73 eq71


@[equational_result]
theorem Equation26828_implies_Equation2 (G : Type*) [Magma G] (h : Equation26828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq23 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq11 eq11
  have eq27 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq23
  have eq88 (X0 X1 X2 : G) : ((((X2 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq27
  have eq101 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq27 eq10
  have eq106 (X0 X2 : G) : ((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0) = X2 := superpose eq88 eq11
  have eq139 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = X2 := superpose eq101 eq106
  have eq150 (X0 X1 : G) : X0 = X1 := superpose eq7 eq139
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq150 eq8
  subsumption eq172 eq150


@[equational_result]
theorem Equation26830_implies_Equation2 (G : Type*) [Magma G] (h : Equation26830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ (X2 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq7 eq11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X2 ◇ X0)) := superpose eq11 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq15 eq18
  have eq20 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq19
  have eq51 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X0 := superpose eq15 eq7
  have eq57 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) = X0 := superpose eq51 eq10
  have eq73 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq57 eq12
  have eq84 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq73 eq20
  have eq113 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq73 eq84
  have eq118 (X0 X1 : G) : X0 = X1 := superpose eq73 eq113
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq120 eq118


@[equational_result]
theorem Equation26831_implies_Equation2 (G : Type*) [Magma G] (h : Equation26831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq27 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq12 eq12
  have eq28 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) = X0 := superpose eq11 eq12
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq27 eq28
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq7 eq48
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq119 eq49


@[equational_result]
theorem Equation26832_implies_Equation2 (G : Type*) [Magma G] (h : Equation26832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq7 eq11
  have eq29 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq12 eq12
  have eq30 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) = X0 := superpose eq11 eq12
  have eq256 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = X0 := superpose eq15 eq29
  have eq307 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq256 eq30
  have eq311 (X0 X4 : G) : X0 = X4 := superpose eq7 eq307
  have eq360 (X0 : G) : sK0 ≠ X0 := superpose eq311 eq8
  subsumption eq360 eq311


@[equational_result]
theorem Equation26835_implies_Equation2 (G : Type*) [Magma G] (h : Equation26835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X2)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3)))) ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X3)))) = (((X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X3))))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X3)))) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq9 eq7
  have eq24 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq17
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X1)) = ((((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0)) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0))) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0)) ◇ X3)))) ◇ X2) := superpose eq11 eq11
  have eq32 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)))) = (((X3 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2))))) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)))) ◇ X3)) ◇ X1) := superpose eq11 eq11
  have eq33 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) = (((X3 ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) ◇ X3)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq7 eq11
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) := superpose eq7 eq11
  have eq45 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X1)) = (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X2) := superpose eq7 eq29
  have eq46 (X1 X3 : G) : (((X3 ◇ X1) ◇ (X1 ◇ X3)) ◇ X1) = X1 := superpose eq7 eq32
  have eq47 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq46 eq45
  have eq49 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq47 eq9
  have eq51 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq47 eq11
  have eq58 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq47 eq21
  have eq64 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq47 eq51
  have eq67 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq47 eq58
  have eq72 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X3)) ◇ X0) := superpose eq47 eq33
  have eq73 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) := superpose eq47 eq72
  have eq81 (X0 X2 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq47 eq36
  have eq82 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq81 eq73
  have eq115 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq64 eq49
  have eq118 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq115 eq67
  have eq148 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq47 eq24
  have eq165 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq118 eq47
  have eq169 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq148 eq165
  have eq170 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq24 eq169
  have eq171 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq170 eq82
  have eq174 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq171 eq170
  have eq176 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq174 eq47
  have eq181 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq174 eq176
  have eq184 (X0 X1 : G) : X0 = X1 := superpose eq181 eq174
  have eq186 (X0 : G) : sK0 ≠ X0 := superpose eq184 eq8
  subsumption eq186 eq184


@[equational_result]
theorem Equation26838_implies_Equation2 (G : Type*) [Magma G] (h : Equation26838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq7 eq11
  have eq50 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X2) ◇ X3) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq7 eq12
  have eq54 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq7 eq12
  have eq68 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0)))))) = (((((X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0)))) ◇ X3) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0))))))) ◇ X2) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0)))) ◇ X3) ◇ X4)) := superpose eq12 eq10
  have eq111 (X0 X3 : G) : (X3 ◇ ((X0 ◇ X3) ◇ (X3 ◇ X0))) = X0 := superpose eq7 eq54
  have eq126 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X3 ◇ X2)) ◇ (X0 ◇ X1)) = X3 := superpose eq54 eq7
  have eq156 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq126 eq50
  have eq200 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X1 := superpose eq111 eq156
  have eq201 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0)))))) = (((X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0)))) ◇ X3) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0)))) ◇ X3) ◇ X4)) := superpose eq200 eq68
  have eq264 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0)))) = ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0)))))) := superpose eq200 eq201
  have eq265 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0)))) = X0 := superpose eq200 eq264
  have eq266 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq200 eq265
  have eq268 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq266 eq200
  have eq271 (X0 X3 : G) : X0 = X3 := superpose eq268 eq268
  have eq290 (X0 : G) : sK0 ≠ X0 := superpose eq271 eq8
  subsumption eq290 eq271


@[equational_result]
theorem Equation26840_implies_Equation2 (G : Type*) [Magma G] (h : Equation26840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X3) := superpose eq11 eq11
  have eq34 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = (((X0 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0)) ◇ (X4 ◇ X0)) := superpose eq11 eq9
  have eq63 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) = X0 := superpose eq18 eq11
  have eq69 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ X0) = (((X3 ◇ X4) ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ X0)))) ◇ (X5 ◇ ((X0 ◇ X1) ◇ ((X3 ◇ X4) ◇ X0)))) := superpose eq18 eq9
  have eq74 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X1 := superpose eq18 eq7
  have eq99 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := superpose eq74 eq34
  have eq100 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X0) = (((X3 ◇ X4) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ (X5 ◇ (X3 ◇ X4))) := superpose eq99 eq69
  have eq122 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ (X5 ◇ (X3 ◇ X4))) := superpose eq99 eq100
  have eq123 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq122 eq11
  have eq124 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq123 eq63
  have eq125 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X0)) = X1 := superpose eq124 eq74
  have eq133 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X1 := superpose eq124 eq125
  have eq134 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq124 eq133
  have eq135 (X0 X3 : G) : X0 = X3 := superpose eq134 eq134
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq135 eq8
  subsumption eq140 eq135


@[equational_result]
theorem Equation26841_implies_Equation2 (G : Type*) [Magma G] (h : Equation26841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq7 eq11
  have eq34 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) = X0 := superpose eq11 eq12
  have eq71 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq15 eq12
  have eq77 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq71 eq34
  have eq131 (X0 X3 : G) : X0 = X3 := superpose eq7 eq77
  have eq239 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq239 eq131


@[equational_result]
theorem Equation26842_implies_Equation2 (G : Type*) [Magma G] (h : Equation26842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = X1 := superpose eq11 eq7
  have eq39 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) ◇ X4) = X0 := superpose eq11 eq12
  have eq53 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq30 eq39
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq53
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq148 eq54


@[equational_result]
theorem Equation26844_implies_Equation2 (G : Type*) [Magma G] (h : Equation26844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X3)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1)) := superpose eq7 eq7
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq46 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = ((((X1 ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3))) ◇ X1) ◇ X1) := superpose eq31 eq31
  have eq52 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ (X1 ◇ (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1))) = X1 := superpose eq31 eq7
  have eq98 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0))) = X0 := superpose eq7 eq52
  have eq200 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq98 eq7
  have eq212 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq98 eq31
  have eq284 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0)) = ((X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0)) ◇ X0)) := superpose eq98 eq200
  have eq286 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq9 eq200
  have eq299 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq200 eq7
  have eq303 (X0 X1 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq200 eq31
  have eq337 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0)) = (X0 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0)) ◇ X0)) := superpose eq98 eq284
  have eq437 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq299 eq31
  have eq439 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X2)) = (((X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) := superpose eq299 eq31
  have eq453 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq299 eq9
  have eq770 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq303
  have eq815 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq303 eq299
  have eq819 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq815 eq770
  have eq821 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq815 eq819
  have eq824 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq821 eq453
  have eq971 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) := superpose eq821 eq31
  have eq1018 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq824 eq971
  have eq1019 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq821 eq1018
  have eq1285 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq200 eq1019
  have eq1324 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq1019 eq31
  have eq1335 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq1019 eq200
  have eq2320 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq1335 eq1285
  have eq2368 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq2320 eq439
  have eq2394 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq2368 eq437
  have eq2397 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq299 eq2394
  have eq2398 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := superpose eq299 eq2397
  have eq2401 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0)) = X0 := superpose eq2398 eq337
  have eq2413 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = (((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3))) ◇ X1) ◇ X1) := superpose eq2401 eq46
  have eq2427 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X1 := superpose eq2320 eq2413
  have eq2430 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ X1)) := superpose eq2427 eq1324
  have eq2493 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq1019 eq2430
  have eq2495 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq2493 eq286
  have eq2812 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq2495 eq31
  have eq2850 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq2320 eq2812
  have eq2912 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq2850 eq2495
  have eq2958 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq2912 eq2320
  have eq2960 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq2958 eq2912
  have eq2961 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose eq2960 eq212
  have eq2991 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq2960 eq2961
  have eq2992 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose eq2960 eq2991
  have eq2993 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq2960 eq2992
  have eq2994 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq2960 eq2993
  have eq3482 (X0 X1 : G) : X0 = X1 := superpose eq2994 eq2960
  have eq3484 (X0 : G) : sK0 ≠ X0 := superpose eq3482 eq8
  subsumption eq3484 eq3482


@[equational_result]
theorem Equation26845_implies_Equation2 (G : Type*) [Magma G] (h : Equation26845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X3)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X3)) = (((X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq7
  have eq26 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) = (((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) := superpose eq10 eq9
  have eq34 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq13 eq13
  have eq37 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq9 eq13
  have eq38 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = (((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ (X1 ◇ X4)) := superpose eq10 eq13
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq13 eq9
  have eq45 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq13 eq7
  have eq57 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq34
  have eq58 (X1 X2 X3 : G) : (X1 ◇ X2) = (X1 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq57 eq45
  have eq59 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq58 eq37
  have eq61 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq58 eq15
  have eq65 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq58 eq59
  have eq68 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) := superpose eq61 eq26
  have eq69 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X4)) = (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) := superpose eq68 eq38
  have eq73 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X3)) = (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X0) := superpose eq68 eq10
  have eq76 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq69 eq11
  have eq78 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := superpose eq73 eq76
  have eq81 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X4)) := superpose eq73 eq69
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq78 eq81
  have eq85 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq83 eq7
  have eq95 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq85 eq65
  have eq97 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq95 eq43
  have eq104 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq95 eq97
  have eq105 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq85 eq104
  have eq106 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq85 eq105
  have eq107 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq106 eq83
  have eq110 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq106 eq107
  have eq141 (X0 X1 : G) : X0 = X1 := superpose eq106 eq110
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq143 eq141


@[equational_result]
theorem Equation26846_implies_Equation2 (G : Type*) [Magma G] (h : Equation26846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (X0 ◇ X3) = ((X0 ◇ ((X0 ◇ X3) ◇ X4)) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X3)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X5)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 X5 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X4)) ◇ (X0 ◇ X5)) = X0 := superpose eq7 eq9
  have eq21 (X0 X5 : G) : (X0 ◇ (X0 ◇ X5)) = X0 := superpose eq7 eq14
  have eq34 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq38 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) = (((X3 ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1)) ◇ (((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ X5)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) := superpose eq10 eq7
  have eq42 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq21
  have eq49 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq21 eq7
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq49 eq42
  have eq64 (X0 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq56 eq34
  have eq67 (X1 X3 X4 X5 : G) : ((X4 ◇ X1) ◇ X1) = (((X3 ◇ ((X4 ◇ X1) ◇ X1)) ◇ (((X4 ◇ X1) ◇ X1) ◇ X5)) ◇ X1) := superpose eq56 eq38
  have eq73 (X1 X4 : G) : ((X4 ◇ X1) ◇ X1) = (((X4 ◇ X1) ◇ X1) ◇ X1) := superpose eq56 eq67
  have eq74 (X1 X4 : G) : ((X4 ◇ X1) ◇ X1) = X1 := superpose eq64 eq73
  have eq93 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq21 eq74
  have eq96 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq21 eq93
  have eq99 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq96 eq56
  have eq102 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq96 eq99
  have eq103 (X0 X1 : G) : X0 = X1 := superpose eq96 eq102
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq103 eq8
  subsumption eq105 eq103


@[equational_result]
theorem Equation26848_implies_Equation2 (G : Type*) [Magma G] (h : Equation26848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ ((X1 ◇ X1) ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X3)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq17 (X0 X1 X3 X4 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (((X4 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X3))) ◇ (X1 ◇ X1)) ◇ (X4 ◇ X4)) := superpose eq7 eq10
  have eq37 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq14 eq14
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq14 eq14
  have eq71 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X3)))) := superpose eq14 eq9
  have eq84 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq9
  have eq93 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))))) := superpose eq9 eq11
  have eq94 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2)))) = (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) ◇ (X0 ◇ X0)) := superpose eq9 eq14
  have eq97 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = ((((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1)) ◇ (((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ X4)) := superpose eq10 eq38
  have eq173 (X0 X1 X3 : G) : (((X3 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3)) = X0 := superpose eq7 eq17
  have eq186 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) := superpose eq14 eq17
  have eq188 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq11 eq17
  have eq192 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq17
  have eq216 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq188
  have eq228 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq11 eq173
  have eq240 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq173
  have eq245 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = (((X1 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq173 eq9
  have eq252 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)))) := superpose eq173 eq10
  have eq266 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq173 eq228
  have eq269 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = ((((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X3)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))))) := superpose eq7 eq84
  have eq322 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq240 eq269
  have eq325 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq322 eq37
  have eq345 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq325 eq71
  have eq347 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq240 eq345
  have eq350 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) ◇ (X0 ◇ X0)) := superpose eq347 eq94
  have eq352 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq347 eq186
  have eq354 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) = ((((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) := superpose eq347 eq97
  have eq370 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)))) = X1 := superpose eq347 eq252
  have eq381 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq347 eq325
  have eq383 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq240 eq352
  have eq388 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = (((X1 ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq383 eq245
  have eq390 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))))) := superpose eq383 eq93
  have eq391 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq192 eq390
  have eq392 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq347 eq391
  have eq399 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq381 eq383
  have eq403 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) = X1 := superpose eq381 eq388
  have eq406 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq347 eq403
  have eq408 (X0 X1 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose eq406 eq370
  have eq434 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq399 eq408
  have eq435 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq434 eq216
  have eq437 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) = (((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) := superpose eq435 eq354
  have eq444 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq435 eq350
  have eq460 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq435 eq392
  have eq470 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq435 eq444
  have eq473 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq460 eq470
  have eq474 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) := superpose eq473 eq437
  have eq491 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq473 eq474
  have eq492 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq434 eq491
  have eq493 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq492 eq266
  have eq499 (X0 X2 : G) : X0 = X2 := superpose eq493 eq493
  have eq519 (X0 : G) : sK0 ≠ X0 := superpose eq499 eq8
  subsumption eq519 eq499


@[equational_result]
theorem Equation26850_implies_Equation2 (G : Type*) [Magma G] (h : Equation26850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq7 eq7
  have eq30 (X0 X2 X5 : G) : ((X0 ◇ (X2 ◇ X5)) ◇ X0) = X2 := superpose eq12 eq12
  have eq42 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq30 eq30
  have eq43 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X1 := superpose eq7 eq30
  have eq129 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = (X4 ◇ ((X1 ◇ X3) ◇ X5)) := superpose eq7 eq42
  have eq190 (X0 X1 X2 X3 X4 X5 : G) : (((((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X5) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = X5 := superpose eq42 eq12
  have eq205 (X1 X3 X4 X5 : G) : (X4 ◇ ((X1 ◇ X3) ◇ X5)) = X1 := superpose eq43 eq129
  have eq226 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq205 eq190
  have eq281 (X0 X4 : G) : X0 = X4 := superpose eq7 eq226
  have eq379 (X0 : G) : sK0 ≠ X0 := superpose eq281 eq8
  subsumption eq379 eq281


@[equational_result]
theorem Equation26853_implies_Equation2 (G : Type*) [Magma G] (h : Equation26853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq9
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq9
  have eq17 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq11
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq17 eq13
  have eq59 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq19
  have eq110 (X0 X2 : G) : X0 = X2 := superpose eq59 eq59
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq110 eq8
  subsumption eq179 eq110


@[equational_result]
theorem Equation26854_implies_Equation2 (G : Type*) [Magma G] (h : Equation26854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X4 X5 : G) : (X1 ◇ X2) = (X0 ◇ (X4 ◇ X5)) := superpose eq7 eq9
  have eq52 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq16
  have eq148 (X0 X4 : G) : X0 = X4 := superpose eq7 eq52
  have eq265 (X0 : G) : sK0 ≠ X0 := superpose eq148 eq8
  subsumption eq265 eq148


@[equational_result]
theorem Equation26856_implies_Equation2 (G : Type*) [Magma G] (h : Equation26856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq7 eq7
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X0)) = X3 := superpose eq11 eq7
  have eq38 (X0 X4 X5 X6 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X6) = X4 := superpose eq12 eq12
  have eq61 (X0 X1 X3 X5 : G) : (X1 ◇ (X5 ◇ X0)) = X3 := superpose eq38 eq26
  have eq178 (X0 X4 : G) : X0 = X4 := superpose eq7 eq61
  have eq284 (X0 : G) : sK0 ≠ X0 := superpose eq178 eq8
  subsumption eq284 eq178


@[equational_result]
theorem Equation26857_implies_Equation2 (G : Type*) [Magma G] (h : Equation26857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X3)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X0) ◇ (X5 ◇ (X4 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X3 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X0) ◇ X3) = (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ (X5 ◇ (X4 ◇ X3))) := superpose eq11 eq10
  have eq16 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X0) ◇ X3) = (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ (X5 ◇ X3)) := superpose eq11 eq13
  have eq17 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X0) ◇ X3) = (((X1 ◇ X3) ◇ X0) ◇ (X5 ◇ X3)) := superpose eq11 eq16
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X2 := superpose eq11 eq12
  have eq19 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X4) ◇ X0) = X2 := superpose eq11 eq18
  have eq20 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X3 := superpose eq19 eq17
  have eq21 (X0 X2 X4 : G) : (X4 ◇ X0) = X2 := superpose eq20 eq19
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq31 eq23


@[equational_result]
theorem Equation26858_implies_Equation2 (G : Type*) [Magma G] (h : Equation26858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) = X2 := superpose eq11 eq7
  have eq33 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq12 eq12
  have eq54 (X1 X2 X4 : G) : (X1 ◇ (X4 ◇ X4)) = X2 := superpose eq33 eq23
  have eq146 (X0 X4 : G) : X0 = X4 := superpose eq7 eq54
  have eq237 (X0 : G) : sK0 ≠ X0 := superpose eq146 eq8
  subsumption eq237 eq146


@[equational_result]
theorem Equation26859_implies_Equation2 (G : Type*) [Magma G] (h : Equation26859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 X5 : G) : (X0 ◇ X2) = (X0 ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X6)) = X3 := superpose eq11 eq7
  have eq33 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X5) = X3 := superpose eq12 eq12
  have eq54 (X1 X3 X5 X6 : G) : (X1 ◇ (X5 ◇ X6)) = X3 := superpose eq33 eq24
  have eq144 (X0 X5 : G) : X0 = X5 := superpose eq7 eq54
  have eq235 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq235 eq144


@[equational_result]
theorem Equation26862_implies_Equation2 (G : Type*) [Magma G] (h : Equation26862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq39 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq7
  have eq45 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq14 eq7
  have eq52 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq14
  have eq53 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq52 eq13
  have eq60 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq52 eq9
  have eq70 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq52 eq45
  have eq71 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq52 eq70
  have eq72 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq71 eq53
  have eq74 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq72 eq60
  have eq78 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq72 eq74
  have eq79 (X0 X3 : G) : X0 = X3 := superpose eq78 eq78
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq81 eq79


@[equational_result]
theorem Equation26865_implies_Equation2 (G : Type*) [Magma G] (h : Equation26865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X3 X4 : G) : ((X3 ◇ X3) ◇ (((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X4)) = X0 := superpose eq7 eq9
  have eq29 (X0 X2 X3 : G) : ((((X0 ◇ X0) ◇ X3) ◇ ((X0 ◇ X0) ◇ X3)) ◇ X2) = X3 := superpose eq10 eq10
  have eq40 (X0 X3 : G) : ((X3 ◇ X3) ◇ X3) = X0 := superpose eq29 eq11
  have eq102 (X0 X2 : G) : X0 = X2 := superpose eq7 eq40
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq118 eq102


@[equational_result]
theorem Equation26867_implies_Equation2 (G : Type*) [Magma G] (h : Equation26867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X0) ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq9
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq32
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq122 eq45


@[equational_result]
theorem Equation26868_implies_Equation2 (G : Type*) [Magma G] (h : Equation26868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ X0) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq44 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq63 (X0 X2 : G) : X0 = X2 := superpose eq7 eq44
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq125 eq63


@[equational_result]
theorem Equation26869_implies_Equation2 (G : Type*) [Magma G] (h : Equation26869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = ((X0 ◇ X0) ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq44 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq125 eq63


@[equational_result]
theorem Equation26872_implies_Equation2 (G : Type*) [Magma G] (h : Equation26872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X2)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) ◇ X1) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)))) ◇ (X1 ◇ X3)) = X1 := superpose eq10 eq7
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2)))) = ((X0 ◇ (((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq31 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)))) = ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)))) ◇ X1) := superpose eq10 eq13
  have eq50 (X0 X1 X2 X3 X4 X5 : G) : (((((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ (((X4 ◇ (((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) ◇ (X4 ◇ X4)) ◇ ((X4 ◇ (((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) ◇ (X4 ◇ X4)))) ◇ ((((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ X5)) = ((((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ ((((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)))) := superpose eq25 eq25
  have eq65 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) ◇ (((X3 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ (X3 ◇ X3)))) = ((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) ◇ (((X4 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ (X4 ◇ X4)) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ (X4 ◇ X4)))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq13 eq25
  have eq70 (X0 X1 X2 X3 X5 : G) : (X0 ◇ X3) = (((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq25 eq9
  have eq77 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = (((X4 ◇ (((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0))) ◇ (X4 ◇ X4)) ◇ (((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) := superpose eq25 eq10
  have eq81 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X0)) := superpose eq25 eq10
  have eq142 (X0 X1 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) = (((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq70 eq13
  have eq144 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))))) = (((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X2 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X2 ◇ X2)))) ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ X3)) := superpose eq70 eq25
  have eq211 (X0 X1 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq70 eq16
  have eq221 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq16
  have eq234 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ ((((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X3 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)))) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X3 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)))))) ◇ (X0 ◇ ((((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X3 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)))) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X3 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)))))))) = (((X0 ◇ X1) ◇ (((X4 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X4)) ◇ ((X4 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X4)))) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq16 eq25
  have eq243 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq221 eq211
  have eq246 (X0 X1 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X0)) = X0 := superpose eq221 eq81
  have eq252 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq7 eq243
  have eq256 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq243 eq70
  have eq257 (X0 X1 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq243 eq9
  have eq258 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ (X0 ◇ X1)) = X0 := superpose eq243 eq16
  have eq260 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ X1) := superpose eq243 eq13
  have eq269 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)))) = (((X0 ◇ (X0 ◇ X0)) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)))) ◇ (X0 ◇ X0)) := superpose eq243 eq25
  have eq276 (X0 X3 X4 X5 : G) : (((((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ (((X4 ◇ (((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) ◇ (X4 ◇ X4)) ◇ ((X4 ◇ (((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) ◇ (X4 ◇ X4)))) ◇ ((((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ X5)) = ((((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq256 eq50
  have eq281 (X0 X3 X4 : G) : (X0 ◇ (X0 ◇ X0)) = (((X4 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X4 ◇ X4)) ◇ (((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) := superpose eq256 eq77
  have eq292 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq246 eq257
  have eq293 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq292 eq252
  have eq297 (X0 X3 X4 X5 : G) : (((((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ (((X4 ◇ (((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) ◇ (X4 ◇ X4)) ◇ ((X4 ◇ (((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) ◇ (X4 ◇ X4)))) ◇ ((((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ X5)) = ((((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) ◇ (X0 ◇ X0)) := superpose eq292 eq276
  have eq299 (X0 X3 X4 : G) : (((X4 ◇ X0) ◇ (X4 ◇ X4)) ◇ (((X3 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) = X0 := superpose eq292 eq281
  have eq309 (X0 X1 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq293 eq142
  have eq311 (X0 X1 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))))) = ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq297 eq144
  have eq312 (X0 X1 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = (((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq311 eq309
  have eq318 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X1)) = X0 := superpose eq292 eq258
  have eq319 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq299 eq318
  have eq322 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X1) := superpose eq292 eq260
  have eq323 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X1) := superpose eq293 eq322
  have eq324 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq323
  have eq325 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq293 eq324
  have eq341 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq13 eq269
  have eq342 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) = (X0 ◇ (X0 ◇ X0)) := superpose eq292 eq341
  have eq343 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose eq292 eq342
  have eq352 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)))) ◇ X1) := superpose eq343 eq31
  have eq368 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2)))))) = (((X0 ◇ X1) ◇ (((X4 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X4)) ◇ ((X4 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X4)))) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq343 eq234
  have eq387 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) = ((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) ◇ (((X4 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ (X4 ◇ X4)) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ (X4 ◇ X4)))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq343 eq65
  have eq477 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq343 eq352
  have eq500 (X0 X1 X2 X5 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2)))))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq343 eq368
  have eq501 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2)))))) := superpose eq319 eq500
  have eq502 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq343 eq501
  have eq503 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq502 eq7
  have eq507 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq502 eq312
  have eq510 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq502 eq343
  have eq512 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq502 eq477
  have eq521 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq512 eq325
  have eq523 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq512 eq507
  have eq589 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) = ((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) ◇ (((X4 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ (X4 ◇ X4)) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ (X4 ◇ X4)))) ◇ (X0 ◇ X1)) := superpose eq502 eq387
  have eq590 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) = ((((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))))) ◇ (X4 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))))))) ◇ (X0 ◇ X1)) := superpose eq502 eq589
  have eq591 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) = (((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)))) ◇ (X0 ◇ X1)) := superpose eq510 eq590
  have eq592 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) := superpose eq502 eq591
  have eq593 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq510 eq592
  have eq595 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq593 eq523
  have eq596 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq593 eq510
  have eq601 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq503 eq595
  have eq602 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq596 eq601
  have eq603 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq602 eq521
  have eq618 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq602 eq603
  have eq619 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq602 eq618
  have eq622 (X0 X1 : G) : X0 = X1 := superpose eq602 eq619
  have eq632 (X0 : G) : sK0 ≠ X0 := superpose eq622 eq8
  subsumption eq632 eq622


@[equational_result]
theorem Equation26875_implies_Equation2 (G : Type*) [Magma G] (h : Equation26875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9
  have eq40 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X3) = X0 := superpose eq7 eq28
  have eq93 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) ◇ X0) = X2 := superpose eq40 eq10
  have eq112 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = X2 := superpose eq40 eq93
  have eq156 (X0 X1 : G) : X0 = X1 := superpose eq7 eq112
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq156 eq8
  subsumption eq173 eq156


@[equational_result]
theorem Equation26877_implies_Equation2 (G : Type*) [Magma G] (h : Equation26877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))))) ◇ X4) = X3 := superpose eq10 eq10
  have eq21 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = X3 := superpose eq10 eq12
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq7 eq21
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq54 eq30


@[equational_result]
theorem Equation26878_implies_Equation2 (G : Type*) [Magma G] (h : Equation26878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X2)) = X1 := superpose eq12 eq10
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq7 eq14
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation26879_implies_Equation2 (G : Type*) [Magma G] (h : Equation26879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X3 ◇ X4)) = X2 := superpose eq12 eq10
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation26881_implies_Equation2 (G : Type*) [Magma G] (h : Equation26881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)))) = X4 := superpose eq7 eq10
  have eq15 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X4) ◇ X3) ◇ (X4 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0))) = X4 := superpose eq7 eq10
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq12 eq9
  have eq52 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq12 eq7
  have eq65 (X0 X1 X2 X3 X4 X5 : G) : ((((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) ◇ X4) ◇ X0) = ((((X4 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2)) ◇ ((((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) ◇ X4) ◇ X0)) ◇ ((X4 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2)) ◇ X5)) ◇ X4) := superpose eq10 eq11
  have eq102 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq7 eq52
  have eq104 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq52 eq52
  have eq107 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq52 eq52
  have eq175 (X0 X1 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq102 eq10
  have eq176 (X0 X1 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq102 eq52
  have eq230 (X0 X1 X2 X4 : G) : ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4) ◇ (X1 ◇ X0)) ◇ (X4 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) = X4 := superpose eq12 eq13
  have eq273 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1))) := superpose eq175 eq15
  have eq284 (X0 X1 X2 X3 : G) : ((((X0 ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X0 ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X2)))) = X3 := superpose eq175 eq10
  have eq481 (X0 X1 : G) : (X1 ◇ X0) = ((((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq176
  have eq482 (X0 X1 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq176
  have eq628 (X0 X1 : G) : (X0 ◇ X0) = ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq12 eq482
  have eq788 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq12 eq49
  have eq1064 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose eq788 eq175
  have eq1404 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))))) := superpose eq102 eq273
  have eq1820 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq104 eq230
  have eq1980 (X0 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq12 eq1820
  have eq1987 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq52 eq1980
  have eq1988 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq1987
  have eq2018 (X0 X1 : G) : (X1 ◇ X0) = (((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq1988 eq481
  have eq2027 (X0 X1 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq1988 eq628
  have eq2077 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose eq1988 eq1064
  have eq2082 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq1988 eq107
  have eq2155 (X0 X1 X2 X3 : G) : ((((X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ X2)))) = X3 := superpose eq1988 eq284
  have eq2192 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq1988 eq1404
  have eq2220 (X0 X1 : G) : (X1 ◇ X0) = ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq1988 eq2018
  have eq2221 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq1988 eq2220
  have eq2230 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq1988 eq2027
  have eq2231 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq1988 eq2230
  have eq2232 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq1988 eq2231
  have eq2247 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq1988 eq2077
  have eq2248 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq1988 eq2247
  have eq2249 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) := superpose eq1988 eq2248
  have eq2255 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq1988 eq2082
  have eq2256 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq2255 eq2249
  have eq2257 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq2232 eq2256
  have eq2406 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq2221 eq2192
  have eq2407 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq2257 eq2406
  have eq2408 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq2257 eq2407
  have eq2413 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2)))) = X3 := superpose eq2408 eq2155
  have eq2459 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X4) ◇ X0) = ((((X4 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0)) ◇ (((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X4) ◇ X0)) ◇ ((X4 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0)) ◇ X5)) ◇ X4) := superpose eq2408 eq65
  have eq3230 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X1)) ◇ X3) = X3 := superpose eq2408 eq2413
  have eq3231 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2)) ◇ X3) ◇ X3) = X3 := superpose eq2408 eq3230
  have eq3232 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2)) ◇ X3) = X3 := superpose eq2408 eq3231
  have eq3233 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq2408 eq3232
  have eq3288 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X4) ◇ X0) = X4 := superpose eq3233 eq2459
  have eq3289 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X0) = X4 := superpose eq2408 eq3288
  have eq3290 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) = X4 := superpose eq2408 eq3289
  have eq3291 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq2408 eq3290
  have eq3292 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq2408 eq3291
  have eq3293 (X0 X3 : G) : X0 = X3 := superpose eq3292 eq3292
  have eq3295 (X0 : G) : sK0 ≠ X0 := superpose eq3293 eq8
  subsumption eq3295 eq3293


@[equational_result]
theorem Equation26882_implies_Equation2 (G : Type*) [Magma G] (h : Equation26882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X3)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X0 ◇ X3))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X4) ◇ X3) ◇ (X4 ◇ (X3 ◇ (X0 ◇ X2)))) = X4 := superpose eq7 eq10
  have eq16 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) := superpose eq7 eq10
  have eq46 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq16
  have eq48 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq16 eq16
  have eq80 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (((X3 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq16 eq11
  have eq112 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq48 eq16
  have eq120 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ X1) := superpose eq48 eq11
  have eq139 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq112
  have eq147 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := superpose eq139 eq120
  have eq179 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X3) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) ◇ (X3 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)))) = X3 := superpose eq7 eq14
  have eq197 (X0 X1 X2 X3 X4 : G) : ((((X4 ◇ X2) ◇ (X4 ◇ X3)) ◇ X0) ◇ X2) = (((((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) ◇ ((((X4 ◇ X2) ◇ (X4 ◇ X3)) ◇ X0) ◇ X2)) ◇ X0) ◇ X0) := superpose eq10 eq14
  have eq198 (X0 X1 X2 X3 X4 X5 : G) : ((((((X5 ◇ X3) ◇ (X5 ◇ X4)) ◇ X2) ◇ X3) ◇ X0) ◇ X2) = (((((((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) ◇ X0) ◇ X2) ◇ ((((((X5 ◇ X3) ◇ (X5 ◇ X4)) ◇ X2) ◇ X3) ◇ X0) ◇ X2)) ◇ X0) ◇ X0) := superpose eq14 eq14
  have eq222 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq139 eq16
  have eq224 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq139 eq11
  have eq254 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq224 eq147
  have eq270 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) = (((X3 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq254 eq80
  have eq289 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X0 := superpose eq254 eq46
  have eq319 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) = X0 := superpose eq289 eq270
  have eq327 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X0 := superpose eq289 eq319
  have eq328 (X0 X1 X2 X3 X4 : G) : ((((X4 ◇ X2) ◇ (X4 ◇ X3)) ◇ X0) ◇ X2) = ((((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq327 eq197
  have eq329 (X0 X1 X2 X3 X4 X5 : G) : ((((((X5 ◇ X3) ◇ (X5 ◇ X4)) ◇ X2) ◇ X3) ◇ X0) ◇ X2) = ((((((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq327 eq198
  have eq330 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X3) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) ◇ (X3 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2))) = X3 := superpose eq327 eq179
  have eq429 (X0 X1 X2 X3 X4 : G) : ((((X4 ◇ X2) ◇ (X4 ◇ X3)) ◇ X0) ◇ X2) = (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq327 eq328
  have eq430 (X0 X1 X2 X4 : G) : (((X4 ◇ X2) ◇ X0) ◇ X2) = (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq327 eq429
  have eq431 (X0 X1 X2 X3 X4 X5 : G) : ((((((X5 ◇ X3) ◇ (X5 ◇ X4)) ◇ X2) ◇ X3) ◇ X0) ◇ X2) = (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq327 eq329
  have eq432 (X0 X1 X2 X3 X5 : G) : (((((X5 ◇ X3) ◇ X2) ◇ X3) ◇ X0) ◇ X2) = (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq327 eq431
  have eq433 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X3) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) ◇ X3) = X3 := superpose eq327 eq330
  have eq434 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X3) = X3 := superpose eq327 eq433
  have eq435 (X0 X2 X3 X5 : G) : (((((X5 ◇ X3) ◇ X2) ◇ X3) ◇ X0) ◇ X2) = X0 := superpose eq434 eq432
  have eq436 (X0 X2 X4 : G) : (((X4 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq434 eq430
  have eq437 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq436 eq435
  have eq438 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq437 eq222
  have eq440 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq438 eq289
  have eq441 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq440 eq436
  have eq452 (X0 X1 : G) : X0 = X1 := superpose eq440 eq441
  have eq462 (X0 : G) : sK0 ≠ X0 := superpose eq452 eq8
  subsumption eq462 eq452


@[equational_result]
theorem Equation26883_implies_Equation2 (G : Type*) [Magma G] (h : Equation26883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X3) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X4)) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X5 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ (X3 ◇ X5)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X3)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X1 ◇ X4)) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X3) = ((X0 ◇ X0) ◇ ((X0 ◇ X3) ◇ X4)) := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X0) ◇ (X4 ◇ X5)) = (((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (X4 ◇ X5))) ◇ X2) ◇ X0) := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X3) ◇ (X2 ◇ X4)) ◇ X0) ◇ X3) = (((X1 ◇ ((((X2 ◇ X3) ◇ (X2 ◇ X4)) ◇ X0) ◇ X3)) ◇ (X1 ◇ X5)) ◇ X0) := superpose eq10 eq7
  have eq24 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (((((X3 ◇ X4) ◇ (X3 ◇ X5)) ◇ X0) ◇ X4) ◇ X6)) ◇ X7)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X8)) := superpose eq10 eq9
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq16 eq16
  have eq88 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ (((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) ◇ X5)) = (((X6 ◇ (X0 ◇ (((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) ◇ X5))) ◇ (X6 ◇ X7)) ◇ (X0 ◇ X4)) := superpose eq10 eq11
  have eq97 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X3)) ◇ X1) := superpose eq16 eq11
  have eq125 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) ◇ X0) := superpose eq49 eq11
  have eq127 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq49 eq7
  have eq145 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq127 eq49
  have eq167 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X3)) ◇ X1) := superpose eq145 eq97
  have eq169 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X0 := superpose eq145 eq125
  have eq175 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq169 eq167
  have eq177 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq175 eq7
  have eq183 (X0 X2 X4 X5 : G) : ((X4 ◇ X0) ◇ (X4 ◇ X5)) = (((X2 ◇ ((X4 ◇ X0) ◇ (X4 ◇ X5))) ◇ X2) ◇ X0) := superpose eq175 eq18
  have eq185 (X0 X1 X3 X5 : G) : ((X3 ◇ X0) ◇ X3) = (((X1 ◇ ((X3 ◇ X0) ◇ X3)) ◇ (X1 ◇ X5)) ◇ X0) := superpose eq175 eq20
  have eq187 (X0 X1 X2 X4 X6 X7 X8 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (((X4 ◇ X0) ◇ X4) ◇ X6)) ◇ X7)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X8)) := superpose eq175 eq24
  have eq189 (X0 X2 X4 X5 X6 X7 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X5)) = (((X6 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X5))) ◇ (X6 ◇ X7)) ◇ (X0 ◇ X4)) := superpose eq175 eq88
  have eq204 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq175 eq183
  have eq206 (X0 X3 : G) : ((X3 ◇ X0) ◇ X3) = (((X3 ◇ X0) ◇ X3) ◇ X0) := superpose eq175 eq185
  have eq207 (X0 X3 : G) : ((X3 ◇ X0) ◇ X3) = X0 := superpose eq204 eq206
  have eq222 (X0 X1 X2 X6 X7 X8 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X6)) ◇ X7)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X8)) := superpose eq207 eq187
  have eq223 (X0 X1 X2 X7 X8 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ (X0 ◇ X7)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X8)) := superpose eq177 eq222
  have eq224 (X0 X1 X2 X8 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X8)) := superpose eq175 eq223
  have eq228 (X0 X2 X4 X5 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X5)) = ((X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X5)) ◇ (X0 ◇ X4)) := superpose eq175 eq189
  have eq229 (X0 X2 X5 : G) : (((X2 ◇ X0) ◇ X2) ◇ X5) = (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X5)) := superpose eq175 eq228
  have eq230 (X0 X2 X5 : G) : ((X2 ◇ X0) ◇ X2) = (((X2 ◇ X0) ◇ X2) ◇ X5) := superpose eq224 eq229
  have eq231 (X0 X5 : G) : (X0 ◇ X5) = X0 := superpose eq207 eq230
  have eq235 (X0 X1 X8 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X8)) := superpose eq231 eq224
  have eq244 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq231 eq235
  have eq250 (X0 X1 : G) : X0 = X1 := superpose eq231 eq244
  have eq260 (X0 : G) : sK0 ≠ X0 := superpose eq250 eq8
  subsumption eq260 eq250


@[equational_result]
theorem Equation26885_implies_Equation2 (G : Type*) [Magma G] (h : Equation26885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq7 eq10
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)))) = X4 := superpose eq7 eq10
  have eq19 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = (((X1 ◇ X1) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)))) := superpose eq7 eq9
  have eq40 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq11 eq7
  have eq72 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq40 eq40
  have eq74 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq11 eq40
  have eq90 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq74 eq72
  have eq144 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq90 eq7
  have eq156 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X2 := superpose eq90 eq7
  have eq180 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq90 eq12
  have eq186 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq90 eq7
  have eq217 (X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4)) = X2 := superpose eq144 eq180
  have eq223 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = (((X1 ◇ X1) ◇ (X1 ◇ X4)) ◇ (X1 ◇ X1)) := superpose eq217 eq19
  have eq249 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq223
  have eq250 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X1) = X3 := superpose eq249 eq10
  have eq340 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) = X2 := superpose eq186 eq156
  have eq368 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = X3 := superpose eq340 eq250
  have eq383 (X0 X2 : G) : X0 = X2 := superpose eq7 eq368
  have eq404 (X0 : G) : sK0 ≠ X0 := superpose eq383 eq8
  subsumption eq404 eq383


@[equational_result]
theorem Equation26886_implies_Equation2 (G : Type*) [Magma G] (h : Equation26886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq15
  have eq83 (X0 X3 : G) : X0 = X3 := superpose eq7 eq36
  have eq190 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq190 eq83


@[equational_result]
theorem Equation26887_implies_Equation2 (G : Type*) [Magma G] (h : Equation26887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X5)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X4)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X0) = X3 := superpose eq7 eq10
  have eq48 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = X2 := superpose eq11 eq17
  have eq122 (X0 X2 : G) : X0 = X2 := superpose eq7 eq48
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq8
  subsumption eq166 eq122


@[equational_result]
theorem Equation26890_implies_Equation2 (G : Type*) [Magma G] (h : Equation26890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq11 eq7
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq9
  have eq47 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X3 ◇ X3)) = ((X4 ◇ X4) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X3 ◇ X3)))) := superpose eq9 eq28
  have eq50 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq28
  have eq66 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq28 eq50
  have eq68 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq66 eq28
  have eq73 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq66 eq14
  have eq132 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq68
  have eq160 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = X2 := superpose eq132 eq73
  have eq164 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X3 ◇ X3)) = ((X4 ◇ X4) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X3 ◇ X3))) := superpose eq132 eq47
  have eq169 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X3 ◇ X3)) = X2 := superpose eq132 eq9
  have eq226 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X3) = ((X4 ◇ X4) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X3)) := superpose eq132 eq164
  have eq227 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X3) = (X4 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X3)) := superpose eq132 eq226
  have eq231 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X3) = X2 := superpose eq132 eq169
  have eq232 (X2 X4 : G) : (X4 ◇ X2) = X2 := superpose eq231 eq227
  have eq236 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X2 := superpose eq232 eq160
  have eq250 (X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = X2 := superpose eq232 eq236
  have eq251 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq232 eq250
  have eq254 (X0 X2 : G) : X0 = X2 := superpose eq251 eq251
  have eq256 (X0 : G) : sK0 ≠ X0 := superpose eq254 eq8
  subsumption eq256 eq254


@[equational_result]
theorem Equation26891_implies_Equation2 (G : Type*) [Magma G] (h : Equation26891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X4)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ (X3 ◇ X5)) ◇ (X0 ◇ (X1 ◇ X2))) = X4 := superpose eq11 eq7
  have eq35 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4)))) ◇ ((X5 ◇ X6) ◇ (X5 ◇ X7)))) ◇ X6) = X3 := superpose eq12 eq12
  have eq63 (X0 X3 X6 : G) : ((X0 ◇ X0) ◇ X6) = X3 := superpose eq24 eq35
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq7 eq63
  have eq192 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq192 eq68


@[equational_result]
theorem Equation26893_implies_Equation2 (G : Type*) [Magma G] (h : Equation26893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X4)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X5 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X4))) = X0 := superpose eq7 eq11
  have eq37 (X0 X4 X5 X6 : G) : (((X0 ◇ X4) ◇ (X0 ◇ X5)) ◇ X6) = X4 := superpose eq7 eq12
  have eq61 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = X0 := superpose eq37 eq13
  have eq64 (X0 X3 X4 : G) : (X4 ◇ X0) = X3 := superpose eq61 eq12
  have eq78 (X0 X3 : G) : X0 = X3 := superpose eq64 eq64
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq80 eq78


@[equational_result]
theorem Equation26894_implies_Equation2 (G : Type*) [Magma G] (h : Equation26894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ (X3 ◇ X2)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq176 eq57


@[equational_result]
theorem Equation26895_implies_Equation2 (G : Type*) [Magma G] (h : Equation26895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ (X5 ◇ X5)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : ((X0 ◇ X0) ◇ (X5 ◇ X5)) = X3 := superpose eq12 eq10
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation26896_implies_Equation2 (G : Type*) [Magma G] (h : Equation26896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X6 X7 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ (X6 ◇ X7)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X6 X7 : G) : ((X0 ◇ X0) ◇ (X6 ◇ X7)) = X3 := superpose eq12 eq10
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation26898_implies_Equation2 (G : Type*) [Magma G] (h : Equation26898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq11
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq10
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq13 eq13
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose eq11 eq13
  have eq40 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := superpose eq13 eq10
  have eq156 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq40
  have eq188 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq156 eq36
  have eq222 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq156 eq188
  have eq229 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq222 eq10
  have eq251 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ X0) := superpose eq222 eq26
  have eq297 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq222 eq229
  have eq298 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq222 eq297
  have eq299 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq222 eq298
  have eq322 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq299 eq251
  have eq323 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq222 eq322
  have eq324 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq222 eq323
  have eq325 (X0 X3 : G) : X0 = X3 := superpose eq324 eq324
  have eq330 (X0 : G) : sK0 ≠ X0 := superpose eq325 eq8
  subsumption eq330 eq325


@[equational_result]
theorem Equation26899_implies_Equation2 (G : Type*) [Magma G] (h : Equation26899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X2 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X0)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq10 eq9
  have eq40 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq34
  have eq53 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq14
  have eq102 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq53 eq9
  have eq108 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq53 eq10
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq53 eq14
  have eq118 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq53 eq11
  have eq119 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq53 eq10
  have eq121 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0)))) = (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) := superpose eq7 eq40
  have eq128 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = ((X0 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq7 eq40
  have eq133 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = ((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X1) ◇ (X2 ◇ X1)) := superpose eq11 eq40
  have eq141 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq53 eq40
  have eq145 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq40 eq7
  have eq146 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = (((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X1) := superpose eq40 eq11
  have eq153 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq40 eq7
  have eq155 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = (((X3 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq40 eq10
  have eq165 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq128 eq118
  have eq166 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq165 eq141
  have eq167 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq145 eq166
  have eq168 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq167 eq102
  have eq171 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose eq167 eq108
  have eq175 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq167 eq116
  have eq180 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq167 eq168
  have eq182 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq180 eq13
  have eq183 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq180 eq12
  have eq186 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq180 eq119
  have eq187 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq180 eq128
  have eq189 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq187 eq40
  have eq192 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X1) ◇ (X2 ◇ X1)) = (X1 ◇ (X2 ◇ X1)) := superpose eq187 eq133
  have eq217 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) = X0 := superpose eq180 eq171
  have eq219 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq180 eq175
  have eq222 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) ◇ X1) := superpose eq187 eq146
  have eq229 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq187 eq153
  have eq231 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = (((X3 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq187 eq155
  have eq262 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq180 eq11
  have eq334 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) := superpose eq186 eq9
  have eq361 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0)))) = (((X2 ◇ X0) ◇ (X3 ◇ X0)) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0)))) := superpose eq7 eq189
  have eq369 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0)) = (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq183 eq189
  have eq376 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq186 eq189
  have eq416 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) = (((X2 ◇ X0) ◇ (X3 ◇ X0)) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0)))) := superpose eq121 eq361
  have eq417 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X1) := superpose eq416 eq222
  have eq425 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq262 eq369
  have eq427 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq187 eq376
  have eq621 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq186 eq187
  have eq675 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq217 eq621
  have eq681 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq675 eq334
  have eq694 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq186 eq681
  have eq698 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq694 eq427
  have eq709 (X0 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq698 eq187
  have eq710 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq698 eq189
  have eq712 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X1) ◇ (X2 ◇ X1)) := superpose eq698 eq192
  have eq721 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq698 eq229
  have eq723 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = (((X3 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose eq698 eq231
  have eq751 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = (((X3 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq694 eq723
  have eq752 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = (((X3 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X0))) := superpose eq709 eq751
  have eq753 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = (((X3 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq710 eq752
  have eq754 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq694 eq753
  have eq755 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X0) = (((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq754 eq721
  have eq760 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X3 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq694 eq755
  have eq783 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq760 eq425
  have eq825 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq698 eq783
  have eq827 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) := superpose eq825 eq417
  have eq853 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) = X0 := superpose eq827 eq219
  have eq855 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = X1 := superpose eq853 eq827
  have eq860 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq855 eq712
  have eq950 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))) = X2 := superpose eq860 eq182
  have eq977 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq860 eq950
  have eq978 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq860 eq977
  have eq979 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq860 eq978
  have eq980 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq860 eq979
  have eq1386 (X0 X2 : G) : X0 = X2 := superpose eq980 eq980
  have eq1394 (X0 : G) : sK0 ≠ X0 := superpose eq1386 eq8
  subsumption eq1394 eq1386


@[equational_result]
theorem Equation26900_implies_Equation2 (G : Type*) [Magma G] (h : Equation26900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ X0) := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq11 eq11
  have eq22 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq15 eq7
  have eq26 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq22 eq22
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq13 eq26
  have eq46 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq26 eq26
  have eq52 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq13 eq46
  have eq54 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq52 eq45
  have eq62 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq52 eq52
  have eq68 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq62 eq54
  have eq76 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq68 eq16
  have eq86 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq68 eq76
  have eq87 (X0 X3 : G) : X0 = X3 := superpose eq86 eq86
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq92 eq87


@[equational_result]
theorem Equation26902_implies_Equation2 (G : Type*) [Magma G] (h : Equation26902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X3) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq10
  have eq27 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq7 eq14
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq11 eq14
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq14 eq10
  have eq39 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq31 eq11
  have eq47 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq39 eq10
  have eq48 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ (X2 ◇ X2)) = X1 := superpose eq39 eq7
  have eq62 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq12 eq47
  have eq63 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq62 eq33
  have eq67 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq63 eq14
  have eq71 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq63 eq27
  have eq78 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X2)) = X1 := superpose eq63 eq48
  have eq79 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X1 := superpose eq67 eq78
  have eq80 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = X1 := superpose eq63 eq79
  have eq81 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq80 eq71
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X1) := superpose eq81 eq10
  have eq85 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq81 eq31
  have eq96 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X2 := superpose eq81 eq83
  have eq100 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X2 := superpose eq85 eq96
  have eq104 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq85 eq100
  have eq105 (X0 X3 : G) : X0 = X3 := superpose eq104 eq104
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq110 eq105


@[equational_result]
theorem Equation26904_implies_Equation2 (G : Type*) [Magma G] (h : Equation26904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ (X4 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X2 ◇ X0) ◇ X0) := superpose eq7 eq11
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq11 eq11
  have eq31 (X0 X3 X4 : G) : (((X4 ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq18 eq12
  have eq38 (X0 X1 X2 X4 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X4) = X0 := superpose eq11 eq31
  have eq40 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq31 eq31
  have eq49 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X4) = X0 := superpose eq40 eq38
  have eq63 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq40 eq49
  have eq64 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq63 eq20
  have eq68 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq63 eq64
  have eq72 (X0 X1 : G) : X0 = X1 := superpose eq63 eq68
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq74 eq72


@[equational_result]
theorem Equation26907_implies_Equation2 (G : Type*) [Magma G] (h : Equation26907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ (X3 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (((X3 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X2 ◇ X0)))) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq9
  have eq22 (X0 X1 X3 X4 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X4 ◇ (((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) ◇ (X1 ◇ (((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))))) ◇ ((X4 ◇ (((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) ◇ (X1 ◇ (((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))))))) := superpose eq10 eq10
  have eq26 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = (((X3 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) ◇ (X2 ◇ X2)) ◇ (((X4 ◇ (X2 ◇ X2)) ◇ X0) ◇ ((X4 ◇ (X2 ◇ X2)) ◇ X0))) := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (((X3 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) ◇ (((X4 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X4 ◇ X2) ◇ (X0 ◇ X2)))) ◇ (((X5 ◇ (((X4 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X4 ◇ X2) ◇ (X0 ◇ X2)))) ◇ (X0 ◇ X0)) ◇ ((X5 ◇ (((X4 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X4 ◇ X2) ◇ (X0 ◇ X2)))) ◇ (X0 ◇ X0)))) := superpose eq10 eq10
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = ((X3 ◇ (X0 ◇ X0)) ◇ (((X4 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X4 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq10 eq9
  have eq34 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq13
  have eq57 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (((X3 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) ◇ (((X4 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X4 ◇ X2) ◇ (X0 ◇ X2)))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq34 eq28
  have eq58 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (((X4 ◇ (X2 ◇ X2)) ◇ X0) ◇ ((X4 ◇ (X2 ◇ X2)) ◇ X0))) := superpose eq34 eq26
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq13 eq57
  have eq61 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose eq59 eq22
  have eq63 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = ((X3 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq59 eq30
  have eq64 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq59 eq61
  have eq65 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq13 eq64
  have eq66 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq65 eq59
  have eq67 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq65 eq34
  have eq72 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq67 eq66
  have eq77 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq65 eq63
  have eq78 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) := superpose eq67 eq77
  have eq80 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq67 eq58
  have eq81 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) := superpose eq72 eq80
  have eq82 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq81
  have eq83 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq82 eq78
  have eq84 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) = X0 := superpose eq83 eq7
  have eq85 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq83 eq65
  have eq90 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq83 eq85
  have eq91 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq90 eq84
  have eq93 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq90 eq91
  have eq98 (X0 X1 : G) : X0 = X1 := superpose eq93 eq90
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq100 eq98


@[equational_result]
theorem Equation26908_implies_Equation2 (G : Type*) [Magma G] (h : Equation26908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ X3)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = X0 := superpose eq11 eq14
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq18 eq18
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq31 eq26


@[equational_result]
theorem Equation26910_implies_Equation2 (G : Type*) [Magma G] (h : Equation26910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = (X0 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X2) := superpose eq7 eq11
  have eq51 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq16
  have eq97 (X0 X3 : G) : X0 = X3 := superpose eq51 eq51
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq169 eq97


@[equational_result]
theorem Equation26911_implies_Equation2 (G : Type*) [Magma G] (h : Equation26911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X6 : G) : (((X1 ◇ X2) ◇ X0) ◇ X6) = X2 := superpose eq11 eq11
  have eq48 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq17 eq17
  have eq107 (X0 X4 : G) : X0 = X4 := superpose eq7 eq48
  have eq247 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq247 eq107


@[equational_result]
theorem Equation26912_implies_Equation2 (G : Type*) [Magma G] (h : Equation26912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X0) = (X0 ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X2) := superpose eq7 eq11
  have eq63 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq16
  have eq136 (X0 X4 : G) : X0 = X4 := superpose eq7 eq63
  have eq245 (X0 : G) : sK0 ≠ X0 := superpose eq136 eq8
  subsumption eq245 eq136


@[equational_result]
theorem Equation26913_implies_Equation2 (G : Type*) [Magma G] (h : Equation26913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 X5 : G) : (X2 ◇ X0) = (X0 ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X2) := superpose eq7 eq11
  have eq62 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq16
  have eq135 (X0 X5 : G) : X0 = X5 := superpose eq7 eq62
  have eq244 (X0 : G) : sK0 ≠ X0 := superpose eq135 eq8
  subsumption eq244 eq135


@[equational_result]
theorem Equation26915_implies_Equation2 (G : Type*) [Magma G] (h : Equation26915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1)))) := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq10
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = ((((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X0) ◇ X0) := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1))) := superpose eq10 eq7
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = (((X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1)))) ◇ (X4 ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1))) ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1))))) ◇ (X5 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1))))))) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1))) ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1))))) ◇ (X5 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1))))))) := superpose eq9 eq9
  have eq64 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X4) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2)))) ◇ (X4 ◇ X0)) = X4 := superpose eq14 eq10
  have eq340 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq12 eq64
  have eq415 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = ((((X2 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ X2) ◇ X2) := superpose eq17 eq17
  have eq453 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq340
  have eq454 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq340 eq7
  have eq463 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq340 eq15
  have eq484 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq340 eq14
  have eq487 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq340 eq15
  have eq491 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq340 eq16
  have eq500 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq454 eq453
  have eq523 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq500 eq463
  have eq524 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq500 eq523
  have eq567 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1))) ◇ X0) := superpose eq524 eq484
  have eq568 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ X0) := superpose eq500 eq567
  have eq569 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ X0) = X0 := superpose eq500 eq568
  have eq574 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0) := superpose eq524 eq487
  have eq575 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X0) := superpose eq500 eq574
  have eq576 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X0) = X0 := superpose eq500 eq575
  have eq583 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X0) ◇ X0) := superpose eq500 eq491
  have eq584 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq569 eq583
  have eq585 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq500 eq584
  have eq586 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq500 eq585
  have eq613 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = ((((X2 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X2) ◇ X2) := superpose eq586 eq415
  have eq765 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X2) ◇ X2) := superpose eq586 eq613
  have eq766 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X2 ◇ X2) := superpose eq576 eq765
  have eq767 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq500 eq766
  have eq772 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X3 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq767 eq20
  have eq852 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq586 eq772
  have eq853 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq586 eq852
  have eq863 (X0 X1 X2 X4 X5 : G) : (X0 ◇ X1) = (((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X4 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ (X5 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))))) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ (X5 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))))) := superpose eq853 eq26
  have eq953 (X0 X1 X2 X4 X5 : G) : (X0 ◇ X1) = (((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X4 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ (X5 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ X1)) := superpose eq853 eq863
  have eq954 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq853 eq953
  have eq955 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq853 eq954
  have eq956 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq853 eq955
  have eq958 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq956 eq767
  have eq966 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq956 eq958
  have eq984 (X0 X1 : G) : X0 = X1 := superpose eq956 eq966
  have eq998 (X0 : G) : sK0 ≠ X0 := superpose eq984 eq8
  subsumption eq998 eq984


@[equational_result]
theorem Equation26917_implies_Equation2 (G : Type*) [Magma G] (h : Equation26917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ ((X2 ◇ X1) ◇ X3)) := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = X0 := superpose eq7 eq11
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq15
  have eq85 (X0 X3 : G) : X0 = X3 := superpose eq15 eq45
  have eq167 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq167 eq85


@[equational_result]
theorem Equation26919_implies_Equation2 (G : Type*) [Magma G] (h : Equation26919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq10 eq10
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq89 eq55


@[equational_result]
theorem Equation26920_implies_Equation2 (G : Type*) [Magma G] (h : Equation26920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq7 eq11
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq15 eq11
  have eq22 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1)))) = X3 := superpose eq21 eq10
  have eq29 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X3 := superpose eq21 eq22
  have eq30 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ X1)) = X3 := superpose eq21 eq29
  have eq31 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X3 := superpose eq21 eq30
  have eq32 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq21 eq31
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq32 eq32
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq38 eq33


@[equational_result]
theorem Equation26921_implies_Equation2 (G : Type*) [Magma G] (h : Equation26921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1)))) ◇ X0) = X3 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq11 eq11
  have eq137 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq22 eq12
  have eq164 (X0 X4 : G) : X0 = X4 := superpose eq7 eq137
  have eq258 (X0 : G) : sK0 ≠ X0 := superpose eq164 eq8
  subsumption eq258 eq164


@[equational_result]
theorem Equation26923_implies_Equation2 (G : Type*) [Magma G] (h : Equation26923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X0) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ X4) = X3 := superpose eq7 eq10
  have eq16 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq10 eq10
  have eq22 (X3 X4 : G) : (X4 ◇ X4) = X3 := superpose eq16 eq11
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq16 eq22
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation26925_implies_Equation2 (G : Type*) [Magma G] (h : Equation26925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ (X2 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ (X4 ◇ X3)) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X5)) = X0 := superpose eq7 eq11
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq13 eq12
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq7 eq32
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq54 eq33


@[equational_result]
theorem Equation26927_implies_Equation2 (G : Type*) [Magma G] (h : Equation26927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq32 (X0 X1 X2 X3 X5 : G) : (X0 ◇ X5) = (X3 ◇ (X1 ◇ X2)) := superpose eq11 eq11
  have eq51 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq32
  have eq163 (X0 X4 : G) : X0 = X4 := superpose eq7 eq51
  have eq311 (X0 : G) : sK0 ≠ X0 := superpose eq163 eq8
  subsumption eq311 eq163


@[equational_result]
theorem Equation26928_implies_Equation2 (G : Type*) [Magma G] (h : Equation26928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X2)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X0 := superpose eq7 eq11
  have eq37 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = X0 := superpose eq16 eq7
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq37 eq37
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq55 eq44


@[equational_result]
theorem Equation26929_implies_Equation2 (G : Type*) [Magma G] (h : Equation26929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq126 eq53


@[equational_result]
theorem Equation26930_implies_Equation2 (G : Type*) [Magma G] (h : Equation26930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (X2 ◇ X1) = (X0 ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq126 eq53


@[equational_result]
theorem Equation26932_implies_Equation2 (G : Type*) [Magma G] (h : Equation26932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq10 eq7
  have eq16 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X4 ◇ X4)))) = X0 := superpose eq7 eq9
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq10 eq9
  have eq28 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq9
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq12 eq28
  have eq33 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq32
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq33 eq27
  have eq35 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq33 eq16
  have eq37 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq33 eq9
  have eq41 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) = X1 := superpose eq33 eq14
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X2) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq33 eq15
  have eq45 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X4 ◇ X4)))) = X0 := superpose eq33 eq20
  have eq51 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq33 eq34
  have eq52 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq35 eq51
  have eq54 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq52 eq37
  have eq55 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq52 eq54
  have eq56 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq33 eq55
  have eq62 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq33 eq41
  have eq63 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) = X1 := superpose eq52 eq62
  have eq64 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = X1 := superpose eq52 eq63
  have eq65 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq52 eq42
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq52 eq65
  have eq67 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq52 eq66
  have eq68 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq52 eq67
  have eq69 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq33 eq68
  have eq70 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq52 eq69
  have eq78 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X4)))) = X0 := superpose eq52 eq45
  have eq79 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X0 ◇ (X4 ◇ X4)))) = X0 := superpose eq52 eq78
  have eq80 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X4))) = X0 := superpose eq70 eq79
  have eq81 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X4)) = X0 := superpose eq33 eq80
  have eq82 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X4)) = X0 := superpose eq52 eq81
  have eq83 (X0 X1 X3 X4 : G) : ((X1 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X4)) = X0 := superpose eq52 eq82
  have eq84 (X0 X1 X3 X4 : G) : ((X1 ◇ X3) ◇ (X0 ◇ X4)) = X0 := superpose eq33 eq83
  have eq85 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq84 eq56
  have eq91 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq85 eq64
  have eq118 (X0 X1 : G) : X0 = X1 := superpose eq85 eq91
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq131 eq118


@[equational_result]
theorem Equation26933_implies_Equation2 (G : Type*) [Magma G] (h : Equation26933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X3)) = (((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : (((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq7
  have eq26 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq12
  have eq27 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq7
  have eq31 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq12 eq7
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq7
  have eq36 (X0 X1 : G) : (((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq26 eq13
  have eq38 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq27 eq36
  have eq44 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) = (((X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq12 eq11
  have eq46 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4)) = (((X5 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) ◇ ((X1 ◇ X4) ◇ (X1 ◇ X4))) ◇ X1) := superpose eq11 eq11
  have eq65 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1)) := superpose eq11 eq7
  have eq86 (X0 X2 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq38 eq11
  have eq88 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq38 eq9
  have eq98 (X0 X2 : G) : (((X2 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq12 eq86
  have eq99 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq12 eq88
  have eq100 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq98 eq99
  have eq104 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq100 eq31
  have eq105 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq100 eq32
  have eq110 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq100 eq44
  have eq118 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq100 eq104
  have eq124 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4)) = (((X5 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) ◇ (X1 ◇ X4)) ◇ X1) := superpose eq118 eq46
  have eq131 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) := superpose eq118 eq65
  have eq148 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X4) = (((X5 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X4)) ◇ (X1 ◇ X4)) ◇ X1) := superpose eq118 eq124
  have eq149 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = (((X5 ◇ (((X0 ◇ X1) ◇ X2) ◇ X4)) ◇ (X1 ◇ X4)) ◇ X1) := superpose eq118 eq148
  have eq163 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq118 eq131
  have eq164 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq118 eq163
  have eq170 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq118 eq105
  have eq171 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq118 eq170
  have eq175 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq118 eq110
  have eq176 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ X0) := superpose eq171 eq175
  have eq177 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq100 eq176
  have eq178 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq118 eq177
  have eq180 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq178 eq164
  have eq186 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ X4) = (((X5 ◇ ((X0 ◇ X1) ◇ X4)) ◇ (X1 ◇ X4)) ◇ X1) := superpose eq178 eq149
  have eq201 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = X1 := superpose eq178 eq180
  have eq202 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq178 eq201
  have eq203 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq178 eq202
  have eq209 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = X1 := superpose eq203 eq186
  have eq210 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq178 eq209
  have eq211 (X0 X3 : G) : X0 = X3 := superpose eq210 eq210
  have eq216 (X0 : G) : sK0 ≠ X0 := superpose eq211 eq8
  subsumption eq216 eq211


@[equational_result]
theorem Equation26934_implies_Equation2 (G : Type*) [Magma G] (h : Equation26934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X0)) = X2 := superpose eq10 eq7
  have eq18 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X3)) = X2 := superpose eq10 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq18 eq13
  have eq20 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq19 eq15
  have eq27 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = X2 := superpose eq19 eq20
  have eq28 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq19 eq27
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq34 eq29


@[equational_result]
theorem Equation26936_implies_Equation2 (G : Type*) [Magma G] (h : Equation26936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose eq10 eq7
  have eq166 (X0 X1 : G) : X0 = X1 := superpose eq7 eq22
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq166 eq8
  subsumption eq207 eq166


@[equational_result]
theorem Equation26937_implies_Equation2 (G : Type*) [Magma G] (h : Equation26937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ (X3 ◇ X3)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq10 eq10
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq10 eq7
  have eq37 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq14 eq14
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq14 eq14
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ X0)) := superpose eq14 eq14
  have eq41 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq14
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq14 eq9
  have eq48 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose eq14 eq10
  have eq51 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = ((X3 ◇ (X4 ◇ X4)) ◇ (((X1 ◇ X3) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X4)) := superpose eq14 eq9
  have eq64 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq13 eq37
  have eq65 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq64 eq40
  have eq66 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq65 eq39
  have eq71 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq66 eq14
  have eq82 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq7 eq45
  have eq85 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq71 eq48
  have eq88 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = ((X3 ◇ (X4 ◇ X4)) ◇ (((X1 ◇ X3) ◇ (X0 ◇ X0)) ◇ X4)) := superpose eq71 eq51
  have eq89 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := superpose eq9 eq88
  have eq91 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq89 eq85
  have eq95 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) := superpose eq89 eq16
  have eq107 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq89 eq41
  have eq115 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq71 eq91
  have eq134 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq107 eq66
  have eq141 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq134 eq95
  have eq143 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq134 eq115
  have eq148 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq143 eq82
  have eq149 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X2)) = X0 := superpose eq148 eq141
  have eq165 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq148 eq149
  have eq166 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq148 eq165
  have eq169 (X0 X2 : G) : X0 = X2 := superpose eq166 eq166
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq169 eq8
  subsumption eq171 eq169


@[equational_result]
theorem Equation26938_implies_Equation2 (G : Type*) [Magma G] (h : Equation26938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) ◇ (X4 ◇ X4)) ◇ X0) = X3 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X4 ◇ X4)) ◇ (X3 ◇ X5)) = X3 := superpose eq10 eq7
  have eq23 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X3 ◇ X4)) = X3 := superpose eq10 eq7
  have eq27 (X3 X4 X5 : G) : (X4 ◇ (X3 ◇ X5)) = X3 := superpose eq23 eq21
  have eq28 (X0 X3 X4 : G) : (X4 ◇ X0) = X3 := superpose eq27 eq11
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq48 eq38


@[equational_result]
theorem Equation26941_implies_Equation2 (G : Type*) [Magma G] (h : Equation26941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation26942_implies_Equation2 (G : Type*) [Magma G] (h : Equation26942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ (X4 ◇ X4)) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X4)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 X4 : G) : ((((X3 ◇ X0) ◇ (X4 ◇ X4)) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X4))) ◇ X0) = X2 := superpose eq11 eq12
  have eq18 (X0 X2 X3 : G) : (((X3 ◇ X0) ◇ (X3 ◇ X0)) ◇ X0) = X2 := superpose eq11 eq17
  have eq19 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = X2 := superpose eq11 eq18
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq40 eq22


@[equational_result]
theorem Equation26944_implies_Equation2 (G : Type*) [Magma G] (h : Equation26944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ X0) := superpose eq7 eq11
  have eq50 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq7 eq30
  have eq130 (X0 X4 : G) : X0 = X4 := superpose eq7 eq50
  have eq303 (X0 : G) : sK0 ≠ X0 := superpose eq130 eq8
  subsumption eq303 eq130


@[equational_result]
theorem Equation26945_implies_Equation2 (G : Type*) [Magma G] (h : Equation26945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ (X3 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X3 ◇ X4))) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ (X3 ◇ X4)) ◇ X0) = X2 := superpose eq10 eq11
  have eq15 (X0 X2 X4 : G) : ((X4 ◇ X4) ◇ X0) = X2 := superpose eq10 eq14
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq36 eq18


@[equational_result]
theorem Equation26946_implies_Equation2 (G : Type*) [Magma G] (h : Equation26946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X2 ◇ X2) = (X0 ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq53 (X0 X1 : G) : X0 = X1 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation26947_implies_Equation2 (G : Type*) [Magma G] (h : Equation26947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 X5 : G) : (X2 ◇ X2) = (X0 ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation26949_implies_Equation2 (G : Type*) [Magma G] (h : Equation26949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3)))) := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X2 ◇ X3)) := superpose eq7 eq11
  have eq37 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = X3 := superpose eq11 eq7
  have eq39 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ X0) := superpose eq29 eq12
  have eq41 (X0 X1 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq29 eq13
  have eq47 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ X0) := superpose eq29 eq39
  have eq48 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq29 eq47
  have eq50 (X0 X1 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X4) ◇ (X0 ◇ X1)) := superpose eq29 eq41
  have eq67 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq37 eq50
  have eq72 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq67 eq48
  have eq78 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq67 eq72
  have eq79 (X0 X2 : G) : X0 = X2 := superpose eq78 eq78
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq81 eq79


@[equational_result]
theorem Equation26950_implies_Equation2 (G : Type*) [Magma G] (h : Equation26950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (X0 ◇ X2) = ((X0 ◇ (X4 ◇ X5)) ◇ ((X0 ◇ X2) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ ((X2 ◇ X3) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X4 ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) := superpose eq11 eq11
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq11
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ X4)) = (((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ (((X0 ◇ X1) ◇ X3) ◇ X5)) ◇ (X0 ◇ X1)) := superpose eq9 eq7
  have eq41 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq11 eq13
  have eq53 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq41 eq34
  have eq55 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X0 := superpose eq53 eq36
  have eq60 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X2 ◇ (X0 ◇ X1)) := superpose eq53 eq16
  have eq73 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq55 eq60
  have eq74 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ X3)) := superpose eq73 eq11
  have eq80 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq73 eq74
  have eq86 (X0 X1 : G) : X0 = X1 := superpose eq80 eq73
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq96 eq86


@[equational_result]
theorem Equation26951_implies_Equation2 (G : Type*) [Magma G] (h : Equation26951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ ((X2 ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X4 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = (X3 ◇ (X0 ◇ X1)) := superpose eq11 eq11
  have eq21 (X0 X1 X3 : G) : (X0 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := superpose eq11 eq16
  have eq24 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X5)) = X2 := superpose eq21 eq10
  have eq26 (X0 X3 X4 : G) : (X4 ◇ (X0 ◇ X3)) = X0 := superpose eq21 eq13
  have eq29 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq26 eq15
  have eq32 (X0 X2 X5 : G) : (X0 ◇ (X0 ◇ X5)) = X2 := superpose eq29 eq24
  have eq37 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq29 eq32
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation26952_implies_Equation2 (G : Type*) [Magma G] (h : Equation26952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X7)) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X2 := superpose eq10 eq10
  have eq38 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq17
  have eq82 (X0 X4 : G) : X0 = X4 := superpose eq10 eq38
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq170 eq82


@[equational_result]
theorem Equation26954_implies_Equation2 (G : Type*) [Magma G] (h : Equation26954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X1) := superpose eq11 eq11
  have eq44 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq28
  have eq134 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq262 (X0 : G) : sK0 ≠ X0 := superpose eq134 eq8
  subsumption eq262 eq134


@[equational_result]
theorem Equation26955_implies_Equation2 (G : Type*) [Magma G] (h : Equation26955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X1) := superpose eq11 eq11
  have eq64 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq21
  have eq169 (X0 X4 : G) : X0 = X4 := superpose eq7 eq64
  have eq321 (X0 : G) : sK0 ≠ X0 := superpose eq169 eq8
  subsumption eq321 eq169


@[equational_result]
theorem Equation26956_implies_Equation2 (G : Type*) [Magma G] (h : Equation26956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X3 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X2) ◇ X1) = (((X0 ◇ X1) ◇ (X4 ◇ X5)) ◇ (X2 ◇ X5)) := superpose eq11 eq7
  have eq46 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X3 := superpose eq10 eq10
  have eq47 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1)) = X3 := superpose eq11 eq10
  have eq57 (X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X1) = X1 := superpose eq47 eq31
  have eq74 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X0) = X3 := superpose eq57 eq46
  have eq88 (X0 X3 X4 : G) : (X4 ◇ X0) = X3 := superpose eq57 eq74
  have eq89 (X0 X3 : G) : X0 = X3 := superpose eq88 eq88
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq105 eq89


@[equational_result]
theorem Equation26957_implies_Equation2 (G : Type*) [Magma G] (h : Equation26957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X7)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X5 : G) : (X2 ◇ X3) = (X0 ◇ ((X1 ◇ X0) ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ (X5 ◇ X6)) ◇ X0) = X4 := superpose eq7 eq7
  have eq50 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1)) = X3 := superpose eq11 eq10
  have eq53 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X0) = X4 := superpose eq50 eq12
  have eq60 (X0 X5 : G) : X0 = X5 := superpose eq7 eq53
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq182 eq60


@[equational_result]
theorem Equation26959_implies_Equation2 (G : Type*) [Magma G] (h : Equation26959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X5 ◇ X4))) = X0 := superpose eq7 eq11
  have eq19 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) := superpose eq7 eq11
  have eq35 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X0 := superpose eq19 eq13
  have eq39 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = X0 := superpose eq35 eq7
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq39 eq39
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq48 eq46


@[equational_result]
theorem Equation26960_implies_Equation2 (G : Type*) [Magma G] (h : Equation26960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq148 eq59


@[equational_result]
theorem Equation26961_implies_Equation2 (G : Type*) [Magma G] (h : Equation26961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X2 ◇ X3)) = X0 := superpose eq10 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation26962_implies_Equation2 (G : Type*) [Magma G] (h : Equation26962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ (X4 ◇ X5)) ◇ X6)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X5 X6 : G) : (X5 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X6)) = X0 := superpose eq7 eq11
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq13 eq12
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq32
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq54 eq33


@[equational_result]
theorem Equation26964_implies_Equation2 (G : Type*) [Magma G] (h : Equation26964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X1) := superpose eq11 eq11
  have eq56 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq21
  have eq155 (X0 X4 : G) : X0 = X4 := superpose eq7 eq56
  have eq302 (X0 : G) : sK0 ≠ X0 := superpose eq155 eq8
  subsumption eq302 eq155


@[equational_result]
theorem Equation26965_implies_Equation2 (G : Type*) [Magma G] (h : Equation26965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X0) ◇ (X4 ◇ X3)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ ((X5 ◇ X0) ◇ (X4 ◇ X3))) ◇ X0) = X2 := superpose eq11 eq12
  have eq18 (X0 X2 X3 X4 X5 : G) : (((X5 ◇ X0) ◇ (X4 ◇ X3)) ◇ X0) = X2 := superpose eq11 eq17
  have eq19 (X0 X2 X3 X4 : G) : ((X4 ◇ X3) ◇ X0) = X2 := superpose eq11 eq18
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq19 eq19
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq40 eq22


@[equational_result]
theorem Equation26966_implies_Equation2 (G : Type*) [Magma G] (h : Equation26966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq137 eq59


@[equational_result]
theorem Equation26967_implies_Equation2 (G : Type*) [Magma G] (h : Equation26967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq73 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq157 eq73


@[equational_result]
theorem Equation26969_implies_Equation2 (G : Type*) [Magma G] (h : Equation26969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X5 ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq7 eq11
  have eq53 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq31
  have eq136 (X0 X5 : G) : X0 = X5 := superpose eq7 eq53
  have eq311 (X0 : G) : sK0 ≠ X0 := superpose eq136 eq8
  subsumption eq311 eq136


@[equational_result]
theorem Equation26970_implies_Equation2 (G : Type*) [Magma G] (h : Equation26970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X5 ◇ X4)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq73 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq157 eq73


@[equational_result]
theorem Equation26971_implies_Equation2 (G : Type*) [Magma G] (h : Equation26971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X5 ◇ X3)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq73 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq157 eq73


@[equational_result]
theorem Equation26972_implies_Equation2 (G : Type*) [Magma G] (h : Equation26972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X5 ◇ X5)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation26973_implies_Equation2 (G : Type*) [Magma G] (h : Equation26973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X6 X7 : G) : (X2 ◇ X3) = (X0 ◇ (X6 ◇ X7)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X6 : G) : X0 = X6 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation26976_implies_Equation2 (G : Type*) [Magma G] (h : Equation26976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq15 eq12
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq15 eq7
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq15 eq14
  have eq22 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X0) = (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ X0) := superpose eq15 eq18
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) := superpose eq15 eq22
  have eq24 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq15 eq23
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq15 eq19
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq24 eq21
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq15 eq26
  have eq28 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq27 eq25
  have eq31 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq27 eq28
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq31 eq27
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation26979_implies_Equation2 (G : Type*) [Magma G] (h : Equation26979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq9
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9
  have eq13 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq9 eq7
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq7
  have eq37 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq11 eq10
  have eq42 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq26 eq37
  have eq43 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq42
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := superpose eq43 eq7
  have eq48 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq43 eq9
  have eq61 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq43 eq47
  have eq72 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq43 eq61
  have eq74 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq72 eq48
  have eq98 (X0 X1 : G) : X0 = X1 := superpose eq74 eq72
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq119 eq98


@[equational_result]
theorem Equation26981_implies_Equation2 (G : Type*) [Magma G] (h : Equation26981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq16 eq12
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq16 eq21
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq16 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation26982_implies_Equation2 (G : Type*) [Magma G] (h : Equation26982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26983_implies_Equation2 (G : Type*) [Magma G] (h : Equation26983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X1 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26986_implies_Equation2 (G : Type*) [Magma G] (h : Equation26986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq16 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq11 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq15 eq14
  have eq26 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq15 eq16
  have eq27 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq26 eq20
  have eq52 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq27 eq11
  have eq54 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq52 eq27
  have eq59 (X0 X1 : G) : X0 = X1 := superpose eq54 eq52
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq61 eq59


@[equational_result]
theorem Equation26989_implies_Equation2 (G : Type*) [Magma G] (h : Equation26989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq10 eq7
  have eq22 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X3)) := superpose eq10 eq9
  have eq57 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq12 eq7
  have eq69 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq57
  have eq79 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := superpose eq69 eq7
  have eq83 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq69 eq14
  have eq84 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X3)) := superpose eq69 eq22
  have eq107 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq69 eq79
  have eq112 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq107 eq83
  have eq113 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X3)) = X1 := superpose eq107 eq84
  have eq131 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq112 eq113
  have eq132 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq112 eq131
  have eq147 (X0 X2 : G) : X0 = X2 := superpose eq132 eq132
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq147 eq8
  subsumption eq155 eq147


@[equational_result]
theorem Equation26991_implies_Equation2 (G : Type*) [Magma G] (h : Equation26991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = X2 := superpose eq10 eq10
  have eq47 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq115 eq47


@[equational_result]
theorem Equation26992_implies_Equation2 (G : Type*) [Magma G] (h : Equation26992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq11
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X2)) = X1 := superpose eq16 eq9
  have eq36 (X0 X2 : G) : X0 = X2 := superpose eq7 eq26
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq57 eq36


@[equational_result]
theorem Equation26993_implies_Equation2 (G : Type*) [Magma G] (h : Equation26993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X1 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation26995_implies_Equation2 (G : Type*) [Magma G] (h : Equation26995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X3)) = (((X1 ◇ X1) ◇ X0) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq7
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq7 eq9
  have eq30 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq13
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) ◇ X0) := superpose eq7 eq13
  have eq39 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq13 eq7
  have eq60 (X0 X1 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq10 eq11
  have eq66 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq10 eq11
  have eq96 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := superpose eq66 eq7
  have eq99 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq66 eq13
  have eq104 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq39 eq99
  have eq105 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq39 eq104
  have eq106 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq105 eq30
  have eq116 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := superpose eq105 eq96
  have eq123 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq106 eq10
  have eq128 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq123 eq106
  have eq130 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq128 eq24
  have eq131 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) ◇ X0) := superpose eq128 eq34
  have eq142 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq128 eq60
  have eq154 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq128 eq13
  have eq173 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X2)) := superpose eq128 eq130
  have eq174 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) := superpose eq128 eq131
  have eq194 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq128 eq142
  have eq195 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq128 eq194
  have eq244 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq128 eq116
  have eq299 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq195 eq154
  have eq307 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq195 eq299
  have eq310 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq307 eq244
  have eq313 (X0 X1 X2 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := superpose eq310 eq173
  have eq317 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq128 eq313
  have eq319 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := superpose eq317 eq174
  have eq353 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq317 eq319
  have eq354 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq353 eq154
  have eq360 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq353 eq354
  have eq365 (X0 X1 : G) : X0 = X1 := superpose eq360 eq353
  have eq378 (X0 : G) : sK0 ≠ X0 := superpose eq365 eq8
  subsumption eq378 eq365


@[equational_result]
theorem Equation26996_implies_Equation2 (G : Type*) [Magma G] (h : Equation26996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X3)) = (((X1 ◇ X1) ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq9 eq7
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq11 eq10
  have eq14 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq13 eq7
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq14
  have eq17 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq15 eq13
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq14 eq17
  have eq28 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq21 eq17
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq15 eq28
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq38 eq30


@[equational_result]
theorem Equation26997_implies_Equation2 (G : Type*) [Magma G] (h : Equation26997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq14 eq13
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq14 eq15
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq24 eq18
  have eq32 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq25
  have eq39 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq32 eq25
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq14 eq39
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq48 eq40


@[equational_result]
theorem Equation26999_implies_Equation2 (G : Type*) [Magma G] (h : Equation26999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X3)) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq10 eq7
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq11 eq9
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq12 eq7
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq10
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq13
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq14 eq12
  have eq18 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq15 eq16
  have eq20 (X0 X1 : G) : X0 = X1 := superpose eq15 eq18
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation27000_implies_Equation2 (G : Type*) [Magma G] (h : Equation27000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = X1 := superpose eq10 eq7
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq10 eq7
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq10
  have eq17 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) = X1 := superpose eq12 eq13
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq16 eq15
  have eq20 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq19
  have eq25 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq12
  have eq30 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq25 eq20
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := superpose eq30 eq7
  have eq36 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq30 eq17
  have eq47 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X1 := superpose eq32 eq32
  have eq64 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq36 eq47
  have eq134 (X0 X2 : G) : X0 = X2 := superpose eq64 eq64
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq134 eq8
  subsumption eq147 eq134


@[equational_result]
theorem Equation27001_implies_Equation2 (G : Type*) [Magma G] (h : Equation27001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X3)) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X3)) = X0 := superpose eq10 eq7
  have eq17 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq15 eq9
  have eq18 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq17 eq11
  have eq23 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq18 eq17
  have eq28 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq18 eq23
  have eq29 (X0 X1 : G) : X0 = X1 := superpose eq18 eq28
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation27004_implies_Equation2 (G : Type*) [Magma G] (h : Equation27004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X3)) = (((X1 ◇ X1) ◇ X0) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq10 eq9
  have eq31 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq10 eq9
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq31 eq17
  have eq46 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq11 eq43
  have eq60 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq46 eq7
  have eq100 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq46 eq60
  have eq109 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq100 eq46
  have eq110 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq100 eq60
  have eq116 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq109 eq110
  have eq119 (X0 X2 : G) : X0 = X2 := superpose eq116 eq116
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq121 eq119


@[equational_result]
theorem Equation27005_implies_Equation2 (G : Type*) [Magma G] (h : Equation27005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq11 eq9
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq11 eq11
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq16 eq14
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation27007_implies_Equation2 (G : Type*) [Magma G] (h : Equation27007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation27008_implies_Equation2 (G : Type*) [Magma G] (h : Equation27008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X1 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation27009_implies_Equation2 (G : Type*) [Magma G] (h : Equation27009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27010_implies_Equation2 (G : Type*) [Magma G] (h : Equation27010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X1 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27013_implies_Equation2 (G : Type*) [Magma G] (h : Equation27013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 : G) : (((((X2 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X1 ◇ X3)) = X1 := superpose eq11 eq7
  have eq39 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq14
  have eq42 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq14 eq14
  have eq43 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) := superpose eq14 eq11
  have eq44 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X1 ◇ X2)) = X1 := superpose eq14 eq9
  have eq69 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq43
  have eq70 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1))) ◇ (X1 ◇ X2)) = X1 := superpose eq39 eq44
  have eq71 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) = X1 := superpose eq42 eq70
  have eq72 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq71 eq69
  have eq78 (X0 X1 X2 X3 : G) : ((((X2 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X3)) = X1 := superpose eq72 eq33
  have eq83 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0) := superpose eq72 eq11
  have eq94 (X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3)) = X1 := superpose eq72 eq78
  have eq95 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X3)) = X1 := superpose eq72 eq94
  have eq100 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq72 eq83
  have eq208 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq100 eq95
  have eq224 (X0 X2 : G) : X0 = X2 := superpose eq208 eq208
  have eq328 (X0 : G) : sK0 ≠ X0 := superpose eq224 eq8
  subsumption eq328 eq224


@[equational_result]
theorem Equation27016_implies_Equation2 (G : Type*) [Magma G] (h : Equation27016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0))) ◇ X0) ◇ X0) = X2 := superpose eq10 eq10
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq9 eq9
  have eq43 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X3) = X0 := superpose eq7 eq28
  have eq98 (X0 X1 X2 : G) : (((((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) ◇ X2) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) ◇ X2)) ◇ X0) ◇ X0) = X2 := superpose eq43 eq14
  have eq119 (X0 X2 : G) : ((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) ◇ X0) = X2 := superpose eq43 eq98
  have eq120 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq43 eq119
  have eq121 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq120 eq7
  have eq126 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq120 eq121
  have eq127 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq120 eq126
  have eq129 (X0 X2 : G) : X0 = X2 := superpose eq127 eq127
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq131 eq129


@[equational_result]
theorem Equation27018_implies_Equation2 (G : Type*) [Magma G] (h : Equation27018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq12 eq11
  have eq26 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq12 eq18
  have eq27 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq12 eq26
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq27
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq34 eq29


@[equational_result]
theorem Equation27019_implies_Equation2 (G : Type*) [Magma G] (h : Equation27019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X2 ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X2)) = X1 := superpose eq12 eq9
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq7 eq14
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq56 eq35


@[equational_result]
theorem Equation27020_implies_Equation2 (G : Type*) [Magma G] (h : Equation27020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X1 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation27023_implies_Equation2 (G : Type*) [Magma G] (h : Equation27023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation27025_implies_Equation2 (G : Type*) [Magma G] (h : Equation27025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq13 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq13 eq11


@[equational_result]
theorem Equation27026_implies_Equation2 (G : Type*) [Magma G] (h : Equation27026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27028_implies_Equation2 (G : Type*) [Magma G] (h : Equation27028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27029_implies_Equation2 (G : Type*) [Magma G] (h : Equation27029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27030_implies_Equation2 (G : Type*) [Magma G] (h : Equation27030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27032_implies_Equation2 (G : Type*) [Magma G] (h : Equation27032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X3)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq13 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq17 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X3)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq12 eq11
  have eq19 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq7
  have eq20 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq12 eq17
  have eq22 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq13
  have eq23 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq19 eq22
  have eq24 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq23 eq20
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq23 eq12
  have eq28 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq23 eq10
  have eq29 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq24
  have eq30 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq29
  have eq31 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq23 eq30
  have eq33 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq23 eq27
  have eq43 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq28 eq33
  have eq52 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq43 eq31
  have eq54 (X0 X2 : G) : X0 = X2 := superpose eq52 eq52
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq62 eq54


@[equational_result]
theorem Equation27034_implies_Equation2 (G : Type*) [Magma G] (h : Equation27034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation27036_implies_Equation2 (G : Type*) [Magma G] (h : Equation27036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27037_implies_Equation2 (G : Type*) [Magma G] (h : Equation27037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27038_implies_Equation2 (G : Type*) [Magma G] (h : Equation27038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27040_implies_Equation2 (G : Type*) [Magma G] (h : Equation27040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27041_implies_Equation2 (G : Type*) [Magma G] (h : Equation27041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27042_implies_Equation2 (G : Type*) [Magma G] (h : Equation27042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27044_implies_Equation2 (G : Type*) [Magma G] (h : Equation27044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27045_implies_Equation2 (G : Type*) [Magma G] (h : Equation27045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27046_implies_Equation2 (G : Type*) [Magma G] (h : Equation27046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27047_implies_Equation2 (G : Type*) [Magma G] (h : Equation27047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27049_implies_Equation2 (G : Type*) [Magma G] (h : Equation27049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq21 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq9
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq9
  have eq25 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq7
  have eq26 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq10
  have eq28 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X3 ◇ ((X2 ◇ X2) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq9 eq7
  have eq30 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq21 eq26
  have eq39 (X0 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) = X0 := superpose eq10 eq21
  have eq42 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq21 eq9
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := superpose eq42 eq22
  have eq53 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq46 eq28
  have eq68 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq46 eq53
  have eq84 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq25 eq9
  have eq97 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := superpose eq46 eq84
  have eq98 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq39 eq97
  have eq100 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq98 eq68
  have eq104 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq98 eq30
  have eq116 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq98 eq100
  have eq124 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq104 eq98
  have eq129 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq124 eq116
  have eq133 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq124 eq129
  have eq149 (X0 X2 : G) : X0 = X2 := superpose eq133 eq133
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq149 eq8
  subsumption eq157 eq149


@[equational_result]
theorem Equation27050_implies_Equation2 (G : Type*) [Magma G] (h : Equation27050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq10 eq7
  have eq20 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq10 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X0))) = (((X3 ◇ X3) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X4 ◇ X4) ◇ X0))) := superpose eq7 eq9
  have eq27 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq9
  have eq29 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X1) ◇ (((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq9 eq7
  have eq33 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq27
  have eq34 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq33
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq34 eq7
  have eq39 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq34 eq12
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq34 eq20
  have eq46 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = (((X3 ◇ X3) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((X4 ◇ X4) ◇ X0))) := superpose eq34 eq21
  have eq52 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq34 eq39
  have eq53 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq34 eq52
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X0))) = X0 := superpose eq53 eq45
  have eq65 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq34 eq64
  have eq66 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = (((X3 ◇ X3) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X4 ◇ X0))) := superpose eq34 eq46
  have eq67 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = ((X3 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X4 ◇ X0))) := superpose eq34 eq66
  have eq77 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq35 eq29
  have eq78 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq34 eq77
  have eq79 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq34 eq78
  have eq81 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X4) ◇ X0)) := superpose eq79 eq67
  have eq90 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq35 eq35
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq90 eq65
  have eq94 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq93 eq81
  have eq103 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq93 eq94
  have eq108 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq103 eq90
  have eq119 (X0 X2 : G) : X0 = X2 := superpose eq108 eq108
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq127 eq119


@[equational_result]
theorem Equation27051_implies_Equation2 (G : Type*) [Magma G] (h : Equation27051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq83 eq32


@[equational_result]
theorem Equation27053_implies_Equation2 (G : Type*) [Magma G] (h : Equation27053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq18 eq18
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq85 eq30


@[equational_result]
theorem Equation27054_implies_Equation2 (G : Type*) [Magma G] (h : Equation27054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq10 eq7
  have eq23 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq12
  have eq28 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq23 eq15
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq23 eq28
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := superpose eq29 eq7
  have eq32 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0)))) := superpose eq29 eq9
  have eq39 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := superpose eq29 eq32
  have eq46 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X2 := superpose eq31 eq31
  have eq53 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ ((X3 ◇ X0) ◇ X3)) = X2 := superpose eq46 eq46
  have eq54 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq31 eq46
  have eq55 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq29 eq46
  have eq59 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq29 eq55
  have eq60 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := superpose eq31 eq59
  have eq73 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ ((X3 ◇ X0) ◇ X3)) = X2 := superpose eq60 eq53
  have eq83 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) = X2 := superpose eq60 eq73
  have eq84 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X2 := superpose eq59 eq83
  have eq85 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq59 eq84
  have eq102 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq29 eq39
  have eq107 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq29 eq39
  have eq121 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq102 eq107
  have eq122 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq85 eq121
  have eq127 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq122 eq54
  have eq150 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq122 eq127
  have eq151 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq122 eq150
  have eq165 (X0 X1 : G) : X0 = X1 := superpose eq29 eq151
  have eq178 (X0 : G) : sK0 ≠ X0 := superpose eq165 eq8
  subsumption eq178 eq165


@[equational_result]
theorem Equation27055_implies_Equation2 (G : Type*) [Magma G] (h : Equation27055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq60 eq16


@[equational_result]
theorem Equation27058_implies_Equation2 (G : Type*) [Magma G] (h : Equation27058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ X0) ◇ (((X2 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X4 ◇ X4) ◇ (X1 ◇ (((X3 ◇ X3) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X2 ◇ X2)))))) ◇ ((X4 ◇ X4) ◇ (X1 ◇ (((X3 ◇ X3) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X2 ◇ X2)))))))) := superpose eq9 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = (((X3 ◇ X3) ◇ (X2 ◇ X2)) ◇ (((X4 ◇ X4) ◇ X0) ◇ ((X4 ◇ X4) ◇ X0))) := superpose eq7 eq9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq10 eq9
  have eq22 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ (((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq9 eq7
  have eq25 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq11
  have eq27 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))))) = ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2)))))) := superpose eq9 eq11
  have eq29 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq11
  have eq41 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq29
  have eq42 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2)))) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))))) := superpose eq41 eq27
  have eq43 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq41 eq25
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) = (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq22 eq42
  have eq46 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq45 eq22
  have eq47 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X4 ◇ X4) ◇ (X1 ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X2 ◇ X2))))) ◇ ((X4 ◇ X4) ◇ (X1 ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X2 ◇ X2))))))) := superpose eq45 eq14
  have eq49 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq43
  have eq52 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X4 ◇ X4) ◇ (X1 ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X2 ◇ X2)))))) := superpose eq49 eq47
  have eq53 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq49 eq18
  have eq54 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = (((X3 ◇ X3) ◇ (X2 ◇ X2)) ◇ ((X4 ◇ X4) ◇ X0)) := superpose eq49 eq16
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := superpose eq49 eq7
  have eq60 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq49 eq46
  have eq71 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X4 ◇ X4) ◇ (X1 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X2))))) := superpose eq49 eq52
  have eq72 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X4 ◇ X4) ◇ (X1 ◇ (X3 ◇ (X0 ◇ X2))))) := superpose eq49 eq71
  have eq73 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X4 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X2))))) := superpose eq49 eq72
  have eq74 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = (X0 ◇ (X4 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X2))))) := superpose eq49 eq73
  have eq75 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X2))))) = X1 := superpose eq49 eq74
  have eq76 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq49 eq53
  have eq77 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq49 eq76
  have eq78 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq49 eq77
  have eq80 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = (((X3 ◇ X3) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X0)) := superpose eq49 eq54
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = (((X3 ◇ X3) ◇ X2) ◇ (X4 ◇ X0)) := superpose eq49 eq80
  have eq82 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = ((X3 ◇ X2) ◇ (X4 ◇ X0)) := superpose eq49 eq81
  have eq83 (X0 X2 X3 X4 : G) : (X2 ◇ X0) = ((X3 ◇ X2) ◇ (X4 ◇ X0)) := superpose eq78 eq82
  have eq84 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X0 := superpose eq49 eq55
  have eq85 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq83 eq60
  have eq86 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := superpose eq49 eq85
  have eq88 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ (X0 ◇ X2)))) = X1 := superpose eq86 eq75
  have eq89 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq86 eq84
  have eq92 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X2))) = X1 := superpose eq86 eq88
  have eq93 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X1 := superpose eq86 eq92
  have eq122 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq89 eq89
  have eq131 (X0 X1 : G) : X0 = X1 := superpose eq122 eq93
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq164 eq131


@[equational_result]
theorem Equation27059_implies_Equation2 (G : Type*) [Magma G] (h : Equation27059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation27061_implies_Equation2 (G : Type*) [Magma G] (h : Equation27061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X4 := superpose eq14 eq12
  have eq27 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq14 eq21
  have eq28 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq14 eq27
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation27062_implies_Equation2 (G : Type*) [Magma G] (h : Equation27062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X3 ◇ X2)) = X0 := superpose eq10 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq10 eq10
  have eq17 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X3) = X0 := superpose eq16 eq13
  have eq21 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq16 eq17
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation27063_implies_Equation2 (G : Type*) [Magma G] (h : Equation27063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27064_implies_Equation2 (G : Type*) [Magma G] (h : Equation27064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27066_implies_Equation2 (G : Type*) [Magma G] (h : Equation27066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X3 ◇ X1)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ (X4 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq7 eq10
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X3 ◇ X1))) = (((((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0)) ◇ (X5 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0))) ◇ (X1 ◇ X1)) := superpose eq10 eq10
  have eq33 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq10 eq10
  have eq49 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq7 eq33
  have eq76 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq33 eq9
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X3 ◇ X1))) = (((((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X1)) := superpose eq49 eq26
  have eq103 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ (X4 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq49 eq24
  have eq115 (X0 X1 X3 X4 : G) : (((X3 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X3 ◇ X1))) = (((((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq49 eq98
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X3 ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))))) ◇ (X4 ◇ X2)) = X4 := superpose eq11 eq11
  have eq165 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X2 ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) ◇ (X3 ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) = X3 := superpose eq11 eq7
  have eq175 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X3 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))))) ◇ (X4 ◇ X2)) = X4 := superpose eq103 eq143
  have eq176 (X0 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X3 ◇ (X0 ◇ X0)))) ◇ (X4 ◇ X2)) = X4 := superpose eq76 eq175
  have eq177 (X2 X3 X4 : G) : (((X2 ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) = X4 := superpose eq9 eq176
  have eq182 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) ◇ (X3 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) = X3 := superpose eq103 eq165
  have eq183 (X0 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq76 eq182
  have eq184 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq177 eq183
  have eq192 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq184 eq184
  have eq220 (X0 X1 X3 X4 : G) : (((X3 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X3 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq192 eq115
  have eq262 (X1 X3 X4 : G) : (((X3 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X3 ◇ X1))) = X1 := superpose eq192 eq220
  have eq263 (X1 X3 : G) : (((X3 ◇ X1) ◇ (X3 ◇ X1)) ◇ X3) = X1 := superpose eq192 eq262
  have eq264 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq192 eq263
  have eq275 (X0 X2 : G) : X0 = X2 := superpose eq264 eq264
  have eq277 (X0 : G) : sK0 ≠ X0 := superpose eq275 eq8
  subsumption eq277 eq275


@[equational_result]
theorem Equation27068_implies_Equation2 (G : Type*) [Magma G] (h : Equation27068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq51 eq34


@[equational_result]
theorem Equation27070_implies_Equation2 (G : Type*) [Magma G] (h : Equation27070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27071_implies_Equation2 (G : Type*) [Magma G] (h : Equation27071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27072_implies_Equation2 (G : Type*) [Magma G] (h : Equation27072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27074_implies_Equation2 (G : Type*) [Magma G] (h : Equation27074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27075_implies_Equation2 (G : Type*) [Magma G] (h : Equation27075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27076_implies_Equation2 (G : Type*) [Magma G] (h : Equation27076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27078_implies_Equation2 (G : Type*) [Magma G] (h : Equation27078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27079_implies_Equation2 (G : Type*) [Magma G] (h : Equation27079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27080_implies_Equation2 (G : Type*) [Magma G] (h : Equation27080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27081_implies_Equation2 (G : Type*) [Magma G] (h : Equation27081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27083_implies_Equation2 (G : Type*) [Magma G] (h : Equation27083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq11
  have eq21 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) = X2 := superpose eq15 eq13
  have eq25 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq15 eq21
  have eq32 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq25 eq15
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq32 eq11
  have eq46 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = X2 := superpose eq45 eq25
  have eq51 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq45 eq46
  have eq54 (X0 X1 : G) : X0 = X1 := superpose eq45 eq51
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq59 eq54


@[equational_result]
theorem Equation27084_implies_Equation2 (G : Type*) [Magma G] (h : Equation27084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq9
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9
  have eq15 (X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X1)) = X1 := superpose eq12 eq11
  have eq22 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq15 eq15
  have eq23 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq15
  have eq27 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq23 eq22
  have eq30 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq23 eq27
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq30 eq9
  have eq34 (X0 X2 : G) : X0 = X2 := superpose eq32 eq32
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq36 eq34


@[equational_result]
theorem Equation27085_implies_Equation2 (G : Type*) [Magma G] (h : Equation27085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq49 eq32


@[equational_result]
theorem Equation27087_implies_Equation2 (G : Type*) [Magma G] (h : Equation27087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27088_implies_Equation2 (G : Type*) [Magma G] (h : Equation27088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27089_implies_Equation2 (G : Type*) [Magma G] (h : Equation27089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27091_implies_Equation2 (G : Type*) [Magma G] (h : Equation27091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27092_implies_Equation2 (G : Type*) [Magma G] (h : Equation27092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27093_implies_Equation2 (G : Type*) [Magma G] (h : Equation27093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27095_implies_Equation2 (G : Type*) [Magma G] (h : Equation27095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27096_implies_Equation2 (G : Type*) [Magma G] (h : Equation27096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27097_implies_Equation2 (G : Type*) [Magma G] (h : Equation27097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27098_implies_Equation2 (G : Type*) [Magma G] (h : Equation27098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27100_implies_Equation2 (G : Type*) [Magma G] (h : Equation27100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq14 eq11
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation27101_implies_Equation2 (G : Type*) [Magma G] (h : Equation27101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X5 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4)))) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X3)) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq17 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X3)) = X1 := superpose eq13 eq12
  have eq19 (X0 X1 X3 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X5 ◇ X3)) = X5 := superpose eq17 eq9
  have eq31 (X0 X1 : G) : X0 = X1 := superpose eq19 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq46 eq31


@[equational_result]
theorem Equation27102_implies_Equation2 (G : Type*) [Magma G] (h : Equation27102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X5 ◇ (X0 ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = X5 := superpose eq10 eq9
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq28 eq21


@[equational_result]
theorem Equation27103_implies_Equation2 (G : Type*) [Magma G] (h : Equation27103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq77 eq23


@[equational_result]
theorem Equation27105_implies_Equation2 (G : Type*) [Magma G] (h : Equation27105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27106_implies_Equation2 (G : Type*) [Magma G] (h : Equation27106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27107_implies_Equation2 (G : Type*) [Magma G] (h : Equation27107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27108_implies_Equation2 (G : Type*) [Magma G] (h : Equation27108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27110_implies_Equation2 (G : Type*) [Magma G] (h : Equation27110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27111_implies_Equation2 (G : Type*) [Magma G] (h : Equation27111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27112_implies_Equation2 (G : Type*) [Magma G] (h : Equation27112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27113_implies_Equation2 (G : Type*) [Magma G] (h : Equation27113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27115_implies_Equation2 (G : Type*) [Magma G] (h : Equation27115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27116_implies_Equation2 (G : Type*) [Magma G] (h : Equation27116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27117_implies_Equation2 (G : Type*) [Magma G] (h : Equation27117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27118_implies_Equation2 (G : Type*) [Magma G] (h : Equation27118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27120_implies_Equation2 (G : Type*) [Magma G] (h : Equation27120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27121_implies_Equation2 (G : Type*) [Magma G] (h : Equation27121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27122_implies_Equation2 (G : Type*) [Magma G] (h : Equation27122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27123_implies_Equation2 (G : Type*) [Magma G] (h : Equation27123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27124_implies_Equation2 (G : Type*) [Magma G] (h : Equation27124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27126_implies_Equation2 (G : Type*) [Magma G] (h : Equation27126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) = X3 := superpose eq14 eq9
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq7
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq14 eq20
  have eq33 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq14 eq21
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq14 eq21
  have eq57 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq23 eq10
  have eq316 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq33 eq57
  have eq346 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq33 eq316
  have eq350 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq346 eq36
  have eq360 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq346 eq350
  have eq363 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq360 eq21
  have eq455 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq360 eq363
  have eq456 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq360 eq455
  have eq541 (X0 X1 : G) : X0 = X1 := superpose eq456 eq360
  have eq543 (X0 : G) : sK0 ≠ X0 := superpose eq541 eq8
  subsumption eq543 eq541


@[equational_result]
theorem Equation27127_implies_Equation2 (G : Type*) [Magma G] (h : Equation27127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq10 eq7
  have eq22 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq10 eq9
  have eq26 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq10
  have eq28 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq22 eq26
  have eq29 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq28
  have eq30 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq29 eq22
  have eq32 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq29 eq12
  have eq39 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq30 eq7
  have eq52 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq30 eq32
  have eq57 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq39 eq39
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq30 eq39
  have eq498 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq52 eq58
  have eq531 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq52 eq498
  have eq534 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq531 eq58
  have eq559 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq531 eq534
  have eq625 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq559 eq57
  have eq688 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq559 eq625
  have eq691 (X0 X2 : G) : X0 = X2 := superpose eq688 eq688
  have eq696 (X0 : G) : sK0 ≠ X0 := superpose eq691 eq8
  subsumption eq696 eq691


@[equational_result]
theorem Equation27128_implies_Equation2 (G : Type*) [Magma G] (h : Equation27128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X4)) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq11 eq7
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq15 eq14
  have eq21 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X4 ◇ X5)) = X4 := superpose eq15 eq9
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq15 eq16
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq24 eq20
  have eq34 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq21 eq21
  have eq37 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq25 eq34
  have eq38 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq37 eq11
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq38 eq37
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation27130_implies_Equation2 (G : Type*) [Magma G] (h : Equation27130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq37 eq14


@[equational_result]
theorem Equation27132_implies_Equation2 (G : Type*) [Magma G] (h : Equation27132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq43 eq16


@[equational_result]
theorem Equation27135_implies_Equation2 (G : Type*) [Magma G] (h : Equation27135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation27136_implies_Equation2 (G : Type*) [Magma G] (h : Equation27136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27138_implies_Equation2 (G : Type*) [Magma G] (h : Equation27138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq36 eq18


@[equational_result]
theorem Equation27139_implies_Equation2 (G : Type*) [Magma G] (h : Equation27139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation27140_implies_Equation2 (G : Type*) [Magma G] (h : Equation27140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27141_implies_Equation2 (G : Type*) [Magma G] (h : Equation27141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27143_implies_Equation2 (G : Type*) [Magma G] (h : Equation27143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X4 ◇ (X1 ◇ X3)) ◇ X5) ◇ X4) ◇ X4) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ (X4 ◇ (X1 ◇ X3))) := superpose eq10 eq10
  have eq14 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ X4) ◇ X0) ◇ X0) := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0)) = (((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X5) ◇ (X1 ◇ X4)) ◇ (X1 ◇ X4)) := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (((X2 ◇ X0) ◇ X4) ◇ X2)) = ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X4)) ◇ ((X2 ◇ X0) ◇ X4)) := superpose eq10 eq10
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ X3) ◇ (X2 ◇ X0)) := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq7
  have eq24 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ (X4 ◇ (X1 ◇ X3))) ◇ (X4 ◇ (X1 ◇ X3))) = X4 := superpose eq10 eq7
  have eq92 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq21 eq22
  have eq97 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X3)) ◇ ((X2 ◇ X0) ◇ X3)) ◇ (((X2 ◇ X0) ◇ X3) ◇ X2)) := superpose eq10 eq22
  have eq106 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((((X0 ◇ X2) ◇ X3) ◇ X0) ◇ X0)) = ((X0 ◇ (((X0 ◇ X2) ◇ X3) ◇ X0)) ◇ (((X0 ◇ X2) ◇ X3) ◇ X0)) := superpose eq22 eq10
  have eq113 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0))) = ((((X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0)) ◇ X4) ◇ X3) ◇ X3) := superpose eq22 eq10
  have eq187 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X3)) ◇ ((X2 ◇ X0) ◇ X3)) = ((((((X2 ◇ X0) ◇ X3) ◇ X2) ◇ X4) ◇ ((X2 ◇ X0) ◇ X3)) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq10 eq14
  have eq232 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0)) = (((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X5) ◇ (((X0 ◇ X1) ◇ X4) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X4) ◇ X0)) := superpose eq14 eq10
  have eq262 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X3) = ((((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ (X4 ◇ (X1 ◇ X3))) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X3)) ◇ ((X1 ◇ X3) ◇ X5)) := superpose eq10 eq92
  have eq266 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X3) ◇ X0) = ((((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X3) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X3) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X3) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X3) ◇ X0) ◇ X5)) := superpose eq14 eq92
  have eq309 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq92 eq9
  have eq338 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = ((X0 ◇ X1) ◇ ((((X0 ◇ X2) ◇ X3) ◇ X0) ◇ X0)) := superpose eq309 eq106
  have eq341 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ X2) = (((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X5) ◇ (((X0 ◇ X1) ◇ X4) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X4) ◇ X0)) := superpose eq338 eq232
  have eq346 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X1) ◇ X3) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X3) ◇ X0) ◇ X5)) := superpose eq341 eq266
  have eq351 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X5) ◇ (X1 ◇ X4)) ◇ (X1 ◇ X4)) := superpose eq346 eq16
  have eq354 (X0 X1 X2 X3 X5 : G) : (X1 ◇ X3) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X1 ◇ X3) ◇ X5)) := superpose eq351 eq262
  have eq355 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X3)) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq354 eq187
  have eq357 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X2 ◇ X0) ◇ (((X2 ◇ X0) ◇ X3) ◇ X2)) := superpose eq355 eq97
  have eq358 (X0 X2 X3 X4 : G) : (X2 ◇ X0) = ((X2 ◇ X3) ◇ (((X2 ◇ X0) ◇ X4) ◇ X2)) := superpose eq355 eq20
  have eq359 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ X3) := superpose eq358 eq357
  have eq364 (X0 X1 X2 X3 X4 X5 : G) : ((((X4 ◇ (X1 ◇ X3)) ◇ X5) ◇ X4) ◇ X4) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X4 ◇ (X1 ◇ X3))) := superpose eq359 eq12
  have eq366 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq359 eq22
  have eq367 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X4 ◇ (X1 ◇ X3))) ◇ (X4 ◇ (X1 ◇ X3))) = X4 := superpose eq359 eq24
  have eq374 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = ((((X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X4) ◇ X3) ◇ X3) := superpose eq359 eq113
  have eq479 (X0 X1 X2 X3 X4 X5 : G) : ((((X4 ◇ (X1 ◇ X3)) ◇ X5) ◇ X4) ◇ X4) = (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (X1 ◇ X3))) := superpose eq359 eq364
  have eq480 (X0 X1 X3 X4 X5 : G) : ((((X4 ◇ (X1 ◇ X3)) ◇ X5) ◇ X4) ◇ X4) = ((X0 ◇ X1) ◇ (X4 ◇ (X1 ◇ X3))) := superpose eq359 eq479
  have eq481 (X0 X1 X3 X4 X5 : G) : (((X4 ◇ (X1 ◇ X3)) ◇ X5) ◇ X4) = ((X0 ◇ X1) ◇ (X4 ◇ (X1 ◇ X3))) := superpose eq359 eq480
  have eq482 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ (X1 ◇ X3))) = ((X4 ◇ (X1 ◇ X3)) ◇ X4) := superpose eq359 eq481
  have eq483 (X0 X1 X3 X4 : G) : (X4 ◇ (X1 ◇ X3)) = ((X0 ◇ X1) ◇ (X4 ◇ (X1 ◇ X3))) := superpose eq359 eq482
  have eq487 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq359 eq366
  have eq488 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq359 eq487
  have eq489 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X4 ◇ (X1 ◇ X3))) = X4 := superpose eq359 eq367
  have eq490 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (X1 ◇ X3))) = X4 := superpose eq359 eq489
  have eq491 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ (X1 ◇ X3))) = X4 := superpose eq359 eq490
  have eq492 (X1 X3 X4 : G) : (X4 ◇ (X1 ◇ X3)) = X4 := superpose eq491 eq483
  have eq494 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = X4 := superpose eq492 eq491
  have eq506 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = X3 := superpose eq494 eq374
  have eq507 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq492 eq506
  have eq509 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq507 eq488
  have eq516 (X0 X2 : G) : X0 = X2 := superpose eq509 eq509
  have eq518 (X0 : G) : sK0 ≠ X0 := superpose eq516 eq8
  subsumption eq518 eq516


@[equational_result]
theorem Equation27145_implies_Equation2 (G : Type*) [Magma G] (h : Equation27145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq13
  have eq23 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X0)) ◇ (X4 ◇ X5)) = X4 := superpose eq19 eq9
  have eq30 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq11 eq23
  have eq32 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq23 eq11
  have eq33 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq30 eq32
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq33 eq11
  have eq65 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq62 eq19
  have eq72 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq62 eq65
  have eq74 (X0 X1 : G) : X0 = X1 := superpose eq72 eq62
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq87 eq74


@[equational_result]
theorem Equation27147_implies_Equation2 (G : Type*) [Magma G] (h : Equation27147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ X1)) = ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := superpose eq7 eq10
  have eq24 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = ((((X2 ◇ X0) ◇ X3) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) := superpose eq10 eq7
  have eq56 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq22
  have eq77 (X0 X2 X4 : G) : (X0 ◇ X4) = (X0 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) := superpose eq56 eq24
  have eq93 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq77 eq77
  have eq133 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq22 eq93
  have eq284 (X0 X3 : G) : X0 = X3 := superpose eq7 eq133
  have eq407 (X0 : G) : sK0 ≠ X0 := superpose eq284 eq8
  subsumption eq407 eq284


@[equational_result]
theorem Equation27148_implies_Equation2 (G : Type*) [Magma G] (h : Equation27148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) ◇ X0) = X3 := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := superpose eq7 eq9
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ X2) := superpose eq28 eq10
  have eq65 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq55 eq7
  have eq119 (X0 X3 : G) : X0 = X3 := superpose eq65 eq65
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq127 eq119


@[equational_result]
theorem Equation27149_implies_Equation2 (G : Type*) [Magma G] (h : Equation27149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X4) ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ ((X1 ◇ X2) ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : ((X1 ◇ X4) ◇ (X0 ◇ X1)) = X1 := superpose eq11 eq10
  have eq17 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X4 := superpose eq13 eq12
  have eq18 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq13 eq17
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq31 eq19


@[equational_result]
theorem Equation27151_implies_Equation2 (G : Type*) [Magma G] (h : Equation27151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X2)) = ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1))) := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := superpose eq7 eq10
  have eq55 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq20 eq20
  have eq129 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq55 eq20
  have eq190 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X2 ◇ X1))) ◇ (((X2 ◇ X1) ◇ X2) ◇ (X2 ◇ X1))) = X3 := superpose eq14 eq7
  have eq267 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq129 eq129
  have eq281 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq129 eq14
  have eq284 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) := superpose eq129 eq55
  have eq390 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq267 eq55
  have eq420 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq390 eq281
  have eq421 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq390 eq267
  have eq422 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq421 eq390
  have eq426 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq422 eq420
  have eq429 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq422 eq426
  have eq430 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq422 eq429
  have eq431 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq430 eq284
  have eq443 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X2 ◇ X1))) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = X3 := superpose eq431 eq190
  have eq747 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1)) = X3 := superpose eq422 eq443
  have eq748 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X3 ◇ X2)) ◇ X2) = X3 := superpose eq431 eq747
  have eq749 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X2) = X3 := superpose eq431 eq748
  have eq750 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq431 eq749
  have eq755 (X0 X3 : G) : X0 = X3 := superpose eq750 eq750
  have eq763 (X0 : G) : sK0 ≠ X0 := superpose eq755 eq8
  subsumption eq763 eq755


@[equational_result]
theorem Equation27153_implies_Equation2 (G : Type*) [Magma G] (h : Equation27153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X3)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation27155_implies_Equation2 (G : Type*) [Magma G] (h : Equation27155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X1 ◇ X2))) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq11
  have eq69 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq161 eq69


@[equational_result]
theorem Equation27156_implies_Equation2 (G : Type*) [Magma G] (h : Equation27156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1)) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq175 eq49


@[equational_result]
theorem Equation27157_implies_Equation2 (G : Type*) [Magma G] (h : Equation27157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq137 eq53


@[equational_result]
theorem Equation27158_implies_Equation2 (G : Type*) [Magma G] (h : Equation27158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27160_implies_Equation2 (G : Type*) [Magma G] (h : Equation27160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X3)) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) = X0 := superpose eq11 eq11
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq7 eq11
  have eq19 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq14
  have eq43 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq9 eq19
  have eq48 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq19 eq7
  have eq53 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq15 eq43
  have eq64 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq19 eq10
  have eq87 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X2) = ((((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) ◇ (((X3 ◇ (X2 ◇ X0)) ◇ X2) ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq10 eq7
  have eq92 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq10 eq19
  have eq93 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq15 eq92
  have eq94 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq93
  have eq95 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq94 eq53
  have eq97 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq95 eq64
  have eq112 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq95 eq48
  have eq123 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq95 eq97
  have eq135 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq95 eq112
  have eq136 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq135 eq123
  have eq138 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq95 eq136
  have eq140 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X3)) = ((X1 ◇ (X0 ◇ X2)) ◇ (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X1)) := superpose eq138 eq10
  have eq148 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = ((((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq138 eq87
  have eq194 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X3)) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) := superpose eq138 eq140
  have eq195 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3)) := superpose eq138 eq194
  have eq196 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X2) = X2 := superpose eq138 eq195
  have eq197 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq138 eq196
  have eq205 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = (((((X0 ◇ X1) ◇ X3) ◇ X4) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4)) ◇ (X0 ◇ X1)) := superpose eq138 eq148
  have eq206 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = ((((X0 ◇ X3) ◇ X4) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4)) ◇ X0) := superpose eq138 eq205
  have eq207 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = X0 := superpose eq197 eq206
  have eq208 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq138 eq207
  have eq209 (X0 X3 : G) : X0 = X3 := superpose eq208 eq208
  have eq214 (X0 : G) : sK0 ≠ X0 := superpose eq209 eq8
  subsumption eq214 eq209


@[equational_result]
theorem Equation27161_implies_Equation2 (G : Type*) [Magma G] (h : Equation27161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ X2)) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X3))) = (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) ◇ X0) := superpose eq9 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (((X4 ◇ X0) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) := superpose eq7 eq10
  have eq31 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq7
  have eq33 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ (X4 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1))) ◇ (X4 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1))) = X4 := superpose eq10 eq9
  have eq47 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) = (((X2 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) := superpose eq9 eq13
  have eq50 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = ((((X4 ◇ (X2 ◇ X1)) ◇ X2) ◇ ((X4 ◇ (X2 ◇ X1)) ◇ X2)) ◇ ((X4 ◇ (X2 ◇ X1)) ◇ X2)) := superpose eq10 eq13
  have eq51 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) := superpose eq13 eq13
  have eq52 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq10 eq13
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X3)) := superpose eq13 eq13
  have eq68 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq13 eq7
  have eq74 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) = X2 := superpose eq7 eq47
  have eq77 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X3))) = (X2 ◇ X0) := superpose eq74 eq15
  have eq82 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq51
  have eq83 (X1 X2 X4 : G) : ((((X4 ◇ (X2 ◇ X1)) ◇ X2) ◇ ((X4 ◇ (X2 ◇ X1)) ◇ X2)) ◇ ((X4 ◇ (X2 ◇ X1)) ◇ X2)) = X2 := superpose eq82 eq50
  have eq85 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) := superpose eq82 eq22
  have eq89 (X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq52 eq31
  have eq91 (X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ (X4 ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X4 ◇ ((X1 ◇ X1) ◇ X1))) = X4 := superpose eq52 eq33
  have eq96 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := superpose eq89 eq53
  have eq99 (X1 X2 X4 : G) : (X4 ◇ ((X4 ◇ (X2 ◇ X1)) ◇ X2)) = X2 := superpose eq96 eq83
  have eq105 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) := superpose eq82 eq68
  have eq106 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X0 ◇ X0) := superpose eq105 eq85
  have eq111 (X2 X4 : G) : (X4 ◇ (X2 ◇ X2)) = X2 := superpose eq106 eq99
  have eq118 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq13 eq77
  have eq130 (X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ X4) ◇ (X4 ◇ ((X1 ◇ X1) ◇ X1))) = X4 := superpose eq118 eq91
  have eq136 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq13 eq111
  have eq137 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq111 eq111
  have eq163 (X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ X4) ◇ (X4 ◇ (X1 ◇ X1))) = X4 := superpose eq137 eq130
  have eq165 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ X0)) := superpose eq137 eq136
  have eq172 (X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ X4) ◇ X1) = X4 := superpose eq111 eq163
  have eq175 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq111 eq165
  have eq178 (X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X1) = X4 := superpose eq175 eq172
  have eq209 (X1 X3 X4 : G) : (X3 ◇ X1) = X4 := superpose eq175 eq178
  have eq210 (X0 X3 : G) : X0 = X3 := superpose eq209 eq209
  have eq215 (X0 : G) : sK0 ≠ X0 := superpose eq210 eq8
  subsumption eq215 eq210


@[equational_result]
theorem Equation27162_implies_Equation2 (G : Type*) [Magma G] (h : Equation27162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq15 eq13
  have eq69 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq19
  have eq76 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq69 eq19
  have eq85 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq69 eq76
  have eq89 (X0 X1 : G) : X0 = X1 := superpose eq85 eq69
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq107 eq89


@[equational_result]
theorem Equation27164_implies_Equation2 (G : Type*) [Magma G] (h : Equation27164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X1 ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X3)) = (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := superpose eq7 eq10
  have eq46 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ X0))) = X4 := superpose eq10 eq7
  have eq65 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq37
  have eq92 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ (((X5 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X5 ◇ (X0 ◇ X0)) ◇ X2)))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X5 ◇ X5))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X5 ◇ X5))))) = X4 := superpose eq10 eq9
  have eq100 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) ◇ (((X4 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X0) ◇ ((X4 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X0))) = X3 := superpose eq37 eq9
  have eq134 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq65 eq37
  have eq161 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) ◇ X0) = X3 := superpose eq134 eq100
  have eq162 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X2)) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X5 ◇ X5))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X5 ◇ X5))))) = X4 := superpose eq134 eq92
  have eq219 (X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X2)) ◇ X3) = X4 := superpose eq161 eq162
  have eq220 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq219 eq65
  have eq227 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) = X4 := superpose eq220 eq46
  have eq271 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X1))) = X4 := superpose eq220 eq227
  have eq272 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ X0) = X4 := superpose eq220 eq271
  have eq273 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq220 eq272
  have eq274 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq220 eq273
  have eq275 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq220 eq274
  have eq276 (X0 X3 : G) : X0 = X3 := superpose eq275 eq275
  have eq278 (X0 : G) : sK0 ≠ X0 := superpose eq276 eq8
  subsumption eq278 eq276


@[equational_result]
theorem Equation27165_implies_Equation2 (G : Type*) [Magma G] (h : Equation27165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X3)) = (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X3)))) = X1 := superpose eq7 eq10
  have eq35 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X0 ◇ X1)) ◇ X2) = ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X3) := superpose eq9 eq10
  have eq40 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = ((X4 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq10 eq35
  have eq47 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X1 := superpose eq40 eq15
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq7 eq47
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq93 eq53


@[equational_result]
theorem Equation27166_implies_Equation2 (G : Type*) [Magma G] (h : Equation27166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation27169_implies_Equation2 (G : Type*) [Magma G] (h : Equation27169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X2 ◇ X2))) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq7 eq9
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq7 eq9
  have eq17 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X3)) = (X3 ◇ X3) := superpose eq13 eq11
  have eq20 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq17 eq7
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation27170_implies_Equation2 (G : Type*) [Magma G] (h : Equation27170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq25 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X2 := superpose eq15 eq11
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq25 eq16
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq62 eq39


@[equational_result]
theorem Equation27172_implies_Equation2 (G : Type*) [Magma G] (h : Equation27172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq56 eq21


@[equational_result]
theorem Equation27173_implies_Equation2 (G : Type*) [Magma G] (h : Equation27173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X2 ◇ X3))) ◇ X0) = X4 := superpose eq7 eq7
  have eq32 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq11
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq32
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq160 eq41


@[equational_result]
theorem Equation27174_implies_Equation2 (G : Type*) [Magma G] (h : Equation27174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq41 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq12 eq12
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq129 eq56


@[equational_result]
theorem Equation27175_implies_Equation2 (G : Type*) [Magma G] (h : Equation27175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27177_implies_Equation2 (G : Type*) [Magma G] (h : Equation27177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X0 ◇ X5)) = (((X1 ◇ X2) ◇ X0) ◇ (((X3 ◇ X4) ◇ (X0 ◇ X5)) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq11
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq57 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq16 eq7
  have eq59 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq16 eq57
  have eq85 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((((X0 ◇ X1) ◇ X4) ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq202 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq59 eq59
  have eq232 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq202
  have eq233 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = (((X0 ◇ X1) ◇ X4) ◇ X0) := superpose eq232 eq85
  have eq310 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X0 ◇ X1) ◇ X0) := superpose eq232 eq233
  have eq311 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = (X0 ◇ X1) := superpose eq232 eq310
  have eq312 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq232 eq311
  have eq313 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq232 eq312
  have eq314 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq232 eq313
  have eq444 (X0 X1 : G) : X0 = X1 := superpose eq314 eq232
  have eq462 (X0 : G) : sK0 ≠ X0 := superpose eq444 eq8
  subsumption eq462 eq444


@[equational_result]
theorem Equation27178_implies_Equation2 (G : Type*) [Magma G] (h : Equation27178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ (X4 ◇ (X0 ◇ X2))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X0 ◇ X5)) = (((X1 ◇ X2) ◇ X0) ◇ (((X3 ◇ X4) ◇ (X0 ◇ X5)) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq7 eq7
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq45 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq15 eq9
  have eq47 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq7
  have eq74 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X5 ◇ X6) ◇ (X2 ◇ X3)) = (((X7 ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X6)) ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4))) := superpose eq10 eq10
  have eq164 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = (X0 ◇ X0) := superpose eq7 eq47
  have eq195 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq15 eq164
  have eq196 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq195 eq45
  have eq213 (X0 X1 X2 X3 X4 X6 X7 : G) : (((X7 ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X6)) ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4))) = X2 := superpose eq195 eq74
  have eq291 (X0 X1 X2 X6 X7 : G) : (((X7 ◇ ((X0 ◇ X1) ◇ X6)) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq196 eq213
  have eq292 (X0 X2 X6 X7 : G) : (((X7 ◇ (X0 ◇ X6)) ◇ X2) ◇ X0) = X2 := superpose eq196 eq291
  have eq293 (X0 X2 X6 X7 : G) : ((X7 ◇ (X0 ◇ X6)) ◇ X0) = X2 := superpose eq196 eq292
  have eq294 (X0 X2 X7 : G) : (X7 ◇ X0) = X2 := superpose eq196 eq293
  have eq295 (X0 X1 : G) : X0 = X1 := superpose eq15 eq294
  have eq303 (X0 : G) : sK0 ≠ X0 := superpose eq295 eq8
  subsumption eq303 eq295


@[equational_result]
theorem Equation27179_implies_Equation2 (G : Type*) [Magma G] (h : Equation27179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X0 ◇ X5)) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq10 eq7
  have eq17 (X0 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (X0 ◇ X5)) = X0 := superpose eq14 eq11
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq17 eq13
  have eq33 (X0 X3 X5 : G) : (X3 ◇ (X0 ◇ X5)) = X0 := superpose eq27 eq17
  have eq37 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq27 eq33
  have eq39 (X0 X1 : G) : X0 = X1 := superpose eq37 eq27
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq57 eq39


@[equational_result]
theorem Equation27180_implies_Equation2 (G : Type*) [Magma G] (h : Equation27180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ (X5 ◇ X7)) = X5 := superpose eq7 eq7
  have eq11 (X0 X5 : G) : (X0 ◇ (X0 ◇ X5)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq15 eq13
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq11 eq9
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq9 eq11
  have eq32 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq29 eq31
  have eq38 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq32
  have eq45 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq38 eq19
  have eq47 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq38 eq45
  have eq48 (X0 X1 : G) : X0 = X1 := superpose eq14 eq47
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq56 eq48


@[equational_result]
theorem Equation27182_implies_Equation2 (G : Type*) [Magma G] (h : Equation27182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq61 eq15


@[equational_result]
theorem Equation27183_implies_Equation2 (G : Type*) [Magma G] (h : Equation27183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X1 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq10
  have eq35 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq10 eq25
  have eq131 (X0 X4 : G) : X0 = X4 := superpose eq7 eq35
  have eq238 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq238 eq131


@[equational_result]
theorem Equation27184_implies_Equation2 (G : Type*) [Magma G] (h : Equation27184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation27185_implies_Equation2 (G : Type*) [Magma G] (h : Equation27185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X5)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation27187_implies_Equation2 (G : Type*) [Magma G] (h : Equation27187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq7 eq11
  have eq27 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq17 eq7
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq38 eq36


@[equational_result]
theorem Equation27188_implies_Equation2 (G : Type*) [Magma G] (h : Equation27188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation27189_implies_Equation2 (G : Type*) [Magma G] (h : Equation27189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X3)) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq54 eq18


@[equational_result]
theorem Equation27190_implies_Equation2 (G : Type*) [Magma G] (h : Equation27190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X5 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X5)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27192_implies_Equation2 (G : Type*) [Magma G] (h : Equation27192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq63 eq18


@[equational_result]
theorem Equation27193_implies_Equation2 (G : Type*) [Magma G] (h : Equation27193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ (X5 ◇ (X3 ◇ X2))) = X4 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X3))) = X3 := superpose eq7 eq7
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq11 eq9
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq41 eq33


@[equational_result]
theorem Equation27194_implies_Equation2 (G : Type*) [Magma G] (h : Equation27194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq32 eq14


@[equational_result]
theorem Equation27195_implies_Equation2 (G : Type*) [Magma G] (h : Equation27195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27197_implies_Equation2 (G : Type*) [Magma G] (h : Equation27197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X5 ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq19 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation27198_implies_Equation2 (G : Type*) [Magma G] (h : Equation27198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X5 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27199_implies_Equation2 (G : Type*) [Magma G] (h : Equation27199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X5 ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27200_implies_Equation2 (G : Type*) [Magma G] (h : Equation27200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X5)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27201_implies_Equation2 (G : Type*) [Magma G] (h : Equation27201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X4 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27203_implies_Equation2 (G : Type*) [Magma G] (h : Equation27203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X1 ◇ X0)) = ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq11 eq7
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq11 eq7
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) := superpose eq7 eq9
  have eq41 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq14
  have eq45 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq7
  have eq56 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = (((((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X4) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0))) ◇ X5) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X4) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0))))) := superpose eq10 eq10
  have eq73 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq9
  have eq76 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X4) ◇ X0) = (((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X4) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq10 eq7
  have eq80 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0))) := superpose eq10 eq14
  have eq81 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq73
  have eq82 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq41 eq41
  have eq85 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq41 eq7
  have eq90 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq41 eq7
  have eq99 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq85 eq82
  have eq102 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq11 eq12
  have eq159 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq85 eq11
  have eq174 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq14 eq18
  have eq187 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq10 eq18
  have eq231 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq99 eq18
  have eq253 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq231 eq159
  have eq254 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq14 eq253
  have eq255 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq254 eq41
  have eq257 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq254 eq85
  have eq258 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq254 eq90
  have eq282 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq257 eq255
  have eq284 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) := superpose eq282 eq19
  have eq290 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq284 eq102
  have eq293 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq290 eq16
  have eq296 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq290 eq45
  have eq307 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq11 eq293
  have eq310 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq296
  have eq316 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq282 eq258
  have eq319 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq316 eq81
  have eq322 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq316 eq174
  have eq324 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq290 eq322
  have eq326 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq324 eq187
  have eq330 (X0 X1 X2 X4 X5 : G) : (X0 ◇ X1) = (((((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X4) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ X1))) ◇ X5) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X4) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ X1))))) := superpose eq326 eq56
  have eq334 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq326 eq76
  have eq338 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq326 eq80
  have eq352 (X0 X1 X2 X5 : G) : (X0 ◇ X1) = (((((((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X5) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq290 eq330
  have eq353 (X0 X1 X5 : G) : (X0 ◇ X1) = (((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X5) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq324 eq352
  have eq354 (X0 X1 X5 : G) : (X0 ◇ X1) = ((((X1 ◇ X0) ◇ X5) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq307 eq353
  have eq355 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq290 eq354
  have eq356 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq307 eq355
  have eq359 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (((((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq290 eq334
  have eq360 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq324 eq359
  have eq361 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq307 eq360
  have eq362 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq361 eq356
  have eq363 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) := superpose eq362 eq338
  have eq364 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq310 eq363
  have eq384 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq364 eq319
  have eq480 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq364 eq384
  have eq481 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X0 := superpose eq364 eq480
  have eq482 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq364 eq481
  have eq483 (X0 X3 : G) : X0 = X3 := superpose eq482 eq482
  have eq488 (X0 : G) : sK0 ≠ X0 := superpose eq483 eq8
  subsumption eq488 eq483


@[equational_result]
theorem Equation27204_implies_Equation2 (G : Type*) [Magma G] (h : Equation27204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq7 eq11
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq11
  have eq28 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X3)) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) = X3 := superpose eq9 eq9
  have eq29 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) := superpose eq7 eq9
  have eq43 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq15 eq7
  have eq85 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq29
  have eq168 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq29 eq43
  have eq198 (X0 X1 : G) : ((((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq43 eq29
  have eq200 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq15 eq168
  have eq256 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq13 eq43
  have eq268 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq200 eq7
  have eq283 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq200 eq11
  have eq294 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq29 eq283
  have eq295 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq268 eq294
  have eq301 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq295 eq85
  have eq302 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq295 eq256
  have eq303 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq295 eq198
  have eq304 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq295 eq29
  have eq395 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq295 eq301
  have eq398 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X3)) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) = X3 := superpose eq395 eq28
  have eq424 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq295 eq302
  have eq425 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq395 eq424
  have eq426 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X0) = X0 := superpose eq295 eq303
  have eq427 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) = X0 := superpose eq295 eq426
  have eq428 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq295 eq427
  have eq431 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq295 eq304
  have eq432 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq431 eq425
  have eq457 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq431 eq428
  have eq459 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq457 eq432
  have eq462 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq459 eq431
  have eq464 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq462 eq398
  have eq576 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X3)) ◇ X3) = X3 := superpose eq462 eq464
  have eq577 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X3 := superpose eq462 eq576
  have eq578 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq462 eq577
  have eq603 (X0 X1 : G) : X0 = X1 := superpose eq462 eq578
  have eq613 (X0 : G) : sK0 ≠ X0 := superpose eq603 eq8
  subsumption eq613 eq603


@[equational_result]
theorem Equation27205_implies_Equation2 (G : Type*) [Magma G] (h : Equation27205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation27207_implies_Equation2 (G : Type*) [Magma G] (h : Equation27207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))))) := superpose eq7 eq10
  have eq55 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq19
  have eq170 (X0 X2 : G) : X0 = X2 := superpose eq55 eq55
  have eq202 (X0 : G) : sK0 ≠ X0 := superpose eq170 eq8
  subsumption eq202 eq170


@[equational_result]
theorem Equation27208_implies_Equation2 (G : Type*) [Magma G] (h : Equation27208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq15
  have eq91 (X0 X3 : G) : X0 = X3 := superpose eq7 eq35
  have eq209 (X0 : G) : sK0 ≠ X0 := superpose eq91 eq8
  subsumption eq209 eq91


@[equational_result]
theorem Equation27209_implies_Equation2 (G : Type*) [Magma G] (h : Equation27209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X4)) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X5)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq9
  have eq19 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X5) = ((((X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X0)) ◇ X4) ◇ X0) ◇ ((X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X0)) ◇ X6)) := superpose eq9 eq7
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X0)) ◇ X4) ◇ X0) ◇ ((X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X0)) ◇ X5)) = X1 := superpose eq17 eq7
  have eq55 (X1 X2 X3 X5 : G) : (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X5) = X1 := superpose eq49 eq19
  have eq98 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq55 eq55
  have eq107 (X0 X4 : G) : X0 = X4 := superpose eq7 eq98
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq156 eq107


@[equational_result]
theorem Equation27212_implies_Equation2 (G : Type*) [Magma G] (h : Equation27212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X0) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ X4) = (((((X5 ◇ X4) ◇ (X5 ◇ X6)) ◇ X1) ◇ X6) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ (X3 ◇ X3))) := superpose eq10 eq10
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X1) ◇ (X4 ◇ X5)) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ (X3 ◇ X3))) = X5 := superpose eq10 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X4) ◇ X3) ◇ (X4 ◇ X4)) ◇ (X2 ◇ X2)) = X2 := superpose eq10 eq7
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (((((X2 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) ◇ X1)) ◇ X5)) ◇ (((X4 ◇ X4) ◇ (X4 ◇ X4)) ◇ ((X4 ◇ X4) ◇ (X4 ◇ X4)))) = X5 := superpose eq10 eq9
  have eq46 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((((X0 ◇ ((X2 ◇ (((X3 ◇ X1) ◇ (X3 ◇ X2)) ◇ X0)) ◇ X4)) ◇ X5) ◇ X4) ◇ (X5 ◇ X5)) := superpose eq9 eq10
  have eq50 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (((((X2 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) ◇ X1)) ◇ X5)) ◇ (X4 ◇ X4)) = X5 := superpose eq19 eq29
  have eq56 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ (X3 ◇ X3)) = ((X4 ◇ X4) ◇ ((((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ (X3 ◇ X3)) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ (X3 ◇ X3)))) := superpose eq10 eq19
  have eq67 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq19 eq9
  have eq79 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq19 eq67
  have eq80 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ (X3 ◇ X3)) = ((X4 ◇ X4) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq79 eq56
  have eq83 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ (X3 ◇ X3)) := superpose eq19 eq80
  have eq86 (X1 X3 X4 X5 X6 : G) : (X4 ◇ X4) = (((((X5 ◇ X4) ◇ (X5 ◇ X6)) ◇ X1) ◇ X6) ◇ (X3 ◇ X3)) := superpose eq83 eq21
  have eq89 (X1 X3 X4 X5 : G) : (((X4 ◇ X1) ◇ (X4 ◇ X5)) ◇ (X3 ◇ X3)) = X5 := superpose eq83 eq24
  have eq95 (X2 X4 : G) : ((X4 ◇ X4) ◇ (X2 ◇ X2)) = X2 := superpose eq83 eq25
  have eq103 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X2 ◇ (((X3 ◇ X1) ◇ (X3 ◇ X2)) ◇ X0)) ◇ X4)) ◇ X5) ◇ X4) ◇ (X5 ◇ X5)) = X1 := superpose eq89 eq46
  have eq104 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = X3 := superpose eq95 eq9
  have eq149 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X1) = ((((X0 ◇ ((X2 ◇ (((X3 ◇ X1) ◇ (X3 ◇ X2)) ◇ X0)) ◇ X4)) ◇ X5) ◇ X4) ◇ (X5 ◇ X5)) := superpose eq104 eq10
  have eq156 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq103 eq149
  have eq165 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ (((((X2 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) ◇ X1)) ◇ X5)) ◇ (X4 ◇ X4)) = X5 := superpose eq156 eq50
  have eq172 (X1 X3 X4 X5 X6 : G) : (X4 ◇ X4) = (((((X5 ◇ X4) ◇ (X5 ◇ X6)) ◇ X1) ◇ X6) ◇ X3) := superpose eq156 eq86
  have eq211 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ (((((X2 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) ◇ X1)) ◇ X5)) ◇ X4) = X5 := superpose eq156 eq165
  have eq216 (X1 X3 X4 X5 X6 : G) : (((((X5 ◇ X4) ◇ (X5 ◇ X6)) ◇ X1) ◇ X6) ◇ X3) = X4 := superpose eq156 eq172
  have eq217 (X0 X1 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X5)) ◇ X4) = X5 := superpose eq216 eq211
  have eq220 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X4) = X5 := superpose eq156 eq217
  have eq221 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = X3 := superpose eq220 eq104
  have eq232 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq156 eq221
  have eq233 (X0 X3 : G) : X0 = X3 := superpose eq232 eq232
  have eq246 (X0 : G) : sK0 ≠ X0 := superpose eq233 eq8
  subsumption eq246 eq233


@[equational_result]
theorem Equation27213_implies_Equation2 (G : Type*) [Magma G] (h : Equation27213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X4)) ◇ ((X2 ◇ X3) ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X0))) ◇ (X1 ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq38 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X1)) ◇ X4)) ◇ X0) = X4 := superpose eq9 eq9
  have eq40 (X0 X1 X5 X6 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X6)) ◇ X5) = X6 := superpose eq9 eq11
  have eq58 (X0 X1 X4 : G) : ((X1 ◇ X1) ◇ X0) = X4 := superpose eq40 eq38
  have eq71 (X0 X3 : G) : X0 = X3 := superpose eq7 eq58
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq149 eq71


@[equational_result]
theorem Equation27215_implies_Equation2 (G : Type*) [Magma G] (h : Equation27215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq45 eq19


@[equational_result]
theorem Equation27216_implies_Equation2 (G : Type*) [Magma G] (h : Equation27216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27217_implies_Equation2 (G : Type*) [Magma G] (h : Equation27217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X4)) ◇ (X5 ◇ X5)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : ((X0 ◇ X0) ◇ (X5 ◇ X5)) = X4 := superpose eq12 eq9
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation27218_implies_Equation2 (G : Type*) [Magma G] (h : Equation27218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X3 := superpose eq7 eq7
  have eq18 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation27220_implies_Equation2 (G : Type*) [Magma G] (h : Equation27220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1)))) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X1 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq25 (X0 X1 X2 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq10 eq7
  have eq35 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X5 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2)))) = X5 := superpose eq10 eq9
  have eq104 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq24 eq7
  have eq257 (X0 X3 X5 : G) : (X0 ◇ (X5 ◇ X3)) = X5 := superpose eq35 eq25
  have eq299 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) = X1 := superpose eq257 eq10
  have eq319 (X0 X2 X3 : G) : (X0 ◇ X3) = ((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq257 eq104
  have eq378 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq257 eq299
  have eq387 (X0 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X0) ◇ X0) := superpose eq257 eq319
  have eq388 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq378 eq387
  have eq392 (X0 X5 : G) : (X0 ◇ X5) = X5 := superpose eq388 eq257
  have eq518 (X0 X1 : G) : X0 = X1 := superpose eq388 eq392
  have eq520 (X0 : G) : sK0 ≠ X0 := superpose eq518 eq8
  subsumption eq520 eq518


@[equational_result]
theorem Equation27222_implies_Equation2 (G : Type*) [Magma G] (h : Equation27222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq14
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation27224_implies_Equation2 (G : Type*) [Magma G] (h : Equation27224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27225_implies_Equation2 (G : Type*) [Magma G] (h : Equation27225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27226_implies_Equation2 (G : Type*) [Magma G] (h : Equation27226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27228_implies_Equation2 (G : Type*) [Magma G] (h : Equation27228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27229_implies_Equation2 (G : Type*) [Magma G] (h : Equation27229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27230_implies_Equation2 (G : Type*) [Magma G] (h : Equation27230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27232_implies_Equation2 (G : Type*) [Magma G] (h : Equation27232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27233_implies_Equation2 (G : Type*) [Magma G] (h : Equation27233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27234_implies_Equation2 (G : Type*) [Magma G] (h : Equation27234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27235_implies_Equation2 (G : Type*) [Magma G] (h : Equation27235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27237_implies_Equation2 (G : Type*) [Magma G] (h : Equation27237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X1 ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X0 := superpose eq9 eq10
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq36 eq36
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq125 eq58


@[equational_result]
theorem Equation27238_implies_Equation2 (G : Type*) [Magma G] (h : Equation27238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq53 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X2 ◇ X1)) = X2 := superpose eq14 eq7
  have eq58 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X3 ◇ X2)) = X3 := superpose eq14 eq7
  have eq68 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X1)) = X2 := superpose eq58 eq53
  have eq69 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq68 eq12
  have eq93 (X0 X3 : G) : ((X0 ◇ X0) ◇ X0) = X3 := superpose eq69 eq9
  have eq99 (X0 X2 : G) : X0 = X2 := superpose eq93 eq93
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq106 eq99


@[equational_result]
theorem Equation27239_implies_Equation2 (G : Type*) [Magma G] (h : Equation27239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation27241_implies_Equation2 (G : Type*) [Magma G] (h : Equation27241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27242_implies_Equation2 (G : Type*) [Magma G] (h : Equation27242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation27243_implies_Equation2 (G : Type*) [Magma G] (h : Equation27243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27245_implies_Equation2 (G : Type*) [Magma G] (h : Equation27245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27246_implies_Equation2 (G : Type*) [Magma G] (h : Equation27246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27247_implies_Equation2 (G : Type*) [Magma G] (h : Equation27247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27249_implies_Equation2 (G : Type*) [Magma G] (h : Equation27249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27250_implies_Equation2 (G : Type*) [Magma G] (h : Equation27250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27251_implies_Equation2 (G : Type*) [Magma G] (h : Equation27251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27252_implies_Equation2 (G : Type*) [Magma G] (h : Equation27252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27254_implies_Equation2 (G : Type*) [Magma G] (h : Equation27254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X4) ◇ (X1 ◇ X5)) = ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq11 eq11
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ X0) := superpose eq11 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4)) = ((((X5 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X6) ◇ ((X5 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X7)) ◇ X5) := superpose eq7 eq12
  have eq22 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = ((((X4 ◇ (X1 ◇ X2)) ◇ X5) ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X6)) ◇ X4) := superpose eq11 eq12
  have eq25 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ X0) = ((((X5 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X6) ◇ ((X5 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X7)) ◇ X5) := superpose eq7 eq12
  have eq26 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = ((((X4 ◇ (X1 ◇ X2)) ◇ X5) ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X6)) ◇ X4) := superpose eq11 eq12
  have eq30 (X0 X2 X3 X4 : G) : ((((X2 ◇ X0) ◇ X3) ◇ ((X2 ◇ X0) ◇ X4)) ◇ X2) = X0 := superpose eq11 eq12
  have eq35 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : ((((X3 ◇ X0) ◇ X4) ◇ X5) ◇ (((X3 ◇ X0) ◇ X4) ◇ X6)) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ ((((X3 ◇ X0) ◇ X7) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X8)) ◇ ((X3 ◇ X0) ◇ X7)) := superpose eq12 eq12
  have eq61 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = (X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4)) := superpose eq18 eq21
  have eq63 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq18 eq22
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ X0) = ((X5 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) ◇ X5) := superpose eq63 eq25
  have eq73 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ X0) := superpose eq16 eq72
  have eq75 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = ((X4 ◇ (X1 ◇ X2)) ◇ X4) := superpose eq63 eq26
  have eq76 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ X3) ◇ X0) := superpose eq16 eq75
  have eq77 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = ((X1 ◇ X2) ◇ X0) := superpose eq76 eq73
  have eq78 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ X2)) := superpose eq76 eq61
  have eq85 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq76 eq30
  have eq86 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = X1 := superpose eq85 eq15
  have eq87 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq86 eq78
  have eq88 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq86 eq77
  have eq102 (X0 X3 X4 X5 X6 : G) : (X3 ◇ X0) = ((((X3 ◇ X0) ◇ X4) ◇ X5) ◇ (((X3 ◇ X0) ◇ X4) ◇ X6)) := superpose eq87 eq35
  have eq103 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = ((((X3 ◇ X0) ◇ X4) ◇ X5) ◇ (X3 ◇ X0)) := superpose eq88 eq102
  have eq104 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq87 eq103
  have eq105 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq104 eq13
  have eq197 (X0 X1 : G) : X0 = X1 := superpose eq104 eq105
  have eq210 (X0 : G) : sK0 ≠ X0 := superpose eq197 eq8
  subsumption eq210 eq197


@[equational_result]
theorem Equation27255_implies_Equation2 (G : Type*) [Magma G] (h : Equation27255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq11 eq7
  have eq29 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = X3 := superpose eq19 eq11
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq36 eq34


@[equational_result]
theorem Equation27256_implies_Equation2 (G : Type*) [Magma G] (h : Equation27256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation27257_implies_Equation2 (G : Type*) [Magma G] (h : Equation27257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation27259_implies_Equation2 (G : Type*) [Magma G] (h : Equation27259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27260_implies_Equation2 (G : Type*) [Magma G] (h : Equation27260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27261_implies_Equation2 (G : Type*) [Magma G] (h : Equation27261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27262_implies_Equation2 (G : Type*) [Magma G] (h : Equation27262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27264_implies_Equation2 (G : Type*) [Magma G] (h : Equation27264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27265_implies_Equation2 (G : Type*) [Magma G] (h : Equation27265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27266_implies_Equation2 (G : Type*) [Magma G] (h : Equation27266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27267_implies_Equation2 (G : Type*) [Magma G] (h : Equation27267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27269_implies_Equation2 (G : Type*) [Magma G] (h : Equation27269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27270_implies_Equation2 (G : Type*) [Magma G] (h : Equation27270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27271_implies_Equation2 (G : Type*) [Magma G] (h : Equation27271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27272_implies_Equation2 (G : Type*) [Magma G] (h : Equation27272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27274_implies_Equation2 (G : Type*) [Magma G] (h : Equation27274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27275_implies_Equation2 (G : Type*) [Magma G] (h : Equation27275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27276_implies_Equation2 (G : Type*) [Magma G] (h : Equation27276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27277_implies_Equation2 (G : Type*) [Magma G] (h : Equation27277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27278_implies_Equation2 (G : Type*) [Magma G] (h : Equation27278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27281_implies_Equation2 (G : Type*) [Magma G] (h : Equation27281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) ◇ X0) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0)))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq10 eq9
  have eq46 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = ((((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X4 ◇ X0)))) ◇ X0) ◇ ((X0 ◇ X4) ◇ ((X3 ◇ X4) ◇ (X4 ◇ X0)))) := superpose eq7 eq14
  have eq50 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq14
  have eq100 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq9 eq50
  have eq104 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq50 eq50
  have eq144 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq104 eq100
  have eq148 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) = (((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq144 eq33
  have eq162 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq144 eq16
  have eq164 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X0)) = ((X3 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq104 eq148
  have eq182 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq104 eq162
  have eq187 (X0 X1 X2 X4 : G) : (X0 ◇ X4) = ((((X1 ◇ X2) ◇ (X2 ◇ X4)) ◇ X0) ◇ ((X0 ◇ X4) ◇ X4)) := superpose eq182 eq46
  have eq209 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ X0) = X1 := superpose eq182 eq164
  have eq224 (X0 X2 X4 : G) : (X0 ◇ X4) = ((X2 ◇ X0) ◇ ((X0 ◇ X4) ◇ X4)) := superpose eq182 eq187
  have eq243 (X0 X2 X4 : G) : (X0 ◇ X4) = ((X2 ◇ X0) ◇ X4) := superpose eq209 eq224
  have eq251 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq209 eq243
  have eq256 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq251 eq209
  have eq263 (X0 X3 : G) : X0 = X3 := superpose eq256 eq256
  have eq265 (X0 : G) : sK0 ≠ X0 := superpose eq263 eq8
  subsumption eq265 eq263


@[equational_result]
theorem Equation27282_implies_Equation2 (G : Type*) [Magma G] (h : Equation27282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X3) ◇ X4)) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X4 ◇ X0)) = (((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X4 ◇ X0)))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X4)) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq9
  have eq21 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq12
  have eq22 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X4)) ◇ X0) = X4 := superpose eq21 eq11
  have eq26 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq21 eq22
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation27285_implies_Equation2 (G : Type*) [Magma G] (h : Equation27285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq11 eq11
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq104 eq36


@[equational_result]
theorem Equation27286_implies_Equation2 (G : Type*) [Magma G] (h : Equation27286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq59 eq21


@[equational_result]
theorem Equation27289_implies_Equation2 (G : Type*) [Magma G] (h : Equation27289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X2) ◇ X3)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq7 eq9
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq7 eq9
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq11
  have eq19 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ X2)) := superpose eq17 eq13
  have eq34 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq19
  have eq70 (X0 X2 : G) : X0 = X2 := superpose eq34 eq34
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq131 eq70


@[equational_result]
theorem Equation27290_implies_Equation2 (G : Type*) [Magma G] (h : Equation27290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ ((X2 ◇ X3) ◇ X5)) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X5)) = X4 := superpose eq7 eq9
  have eq52 (X0 X5 : G) : X0 = X5 := superpose eq7 eq14
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq168 eq52


@[equational_result]
theorem Equation27292_implies_Equation2 (G : Type*) [Magma G] (h : Equation27292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation27293_implies_Equation2 (G : Type*) [Magma G] (h : Equation27293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq109 eq39


@[equational_result]
theorem Equation27294_implies_Equation2 (G : Type*) [Magma G] (h : Equation27294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq42 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq12 eq12
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq42
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq130 eq57


@[equational_result]
theorem Equation27295_implies_Equation2 (G : Type*) [Magma G] (h : Equation27295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27299_implies_Equation2 (G : Type*) [Magma G] (h : Equation27299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation27301_implies_Equation2 (G : Type*) [Magma G] (h : Equation27301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27302_implies_Equation2 (G : Type*) [Magma G] (h : Equation27302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27303_implies_Equation2 (G : Type*) [Magma G] (h : Equation27303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27305_implies_Equation2 (G : Type*) [Magma G] (h : Equation27305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27306_implies_Equation2 (G : Type*) [Magma G] (h : Equation27306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27307_implies_Equation2 (G : Type*) [Magma G] (h : Equation27307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27309_implies_Equation2 (G : Type*) [Magma G] (h : Equation27309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27310_implies_Equation2 (G : Type*) [Magma G] (h : Equation27310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27311_implies_Equation2 (G : Type*) [Magma G] (h : Equation27311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27312_implies_Equation2 (G : Type*) [Magma G] (h : Equation27312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27315_implies_Equation2 (G : Type*) [Magma G] (h : Equation27315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X2 ◇ X2)) = (((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((X2 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq10 eq10
  have eq35 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X1)) ◇ (X3 ◇ (X2 ◇ X2))) = X3 := superpose eq10 eq9
  have eq52 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = ((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) := superpose eq7 eq33
  have eq57 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3)) = ((X4 ◇ X3) ◇ (X3 ◇ X3)) := superpose eq10 eq33
  have eq108 (X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X1)) ◇ (X3 ◇ (X2 ◇ X2))) = X3 := superpose eq52 eq35
  have eq158 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq179 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq9 eq158
  have eq183 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq158 eq158
  have eq194 (X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X2 ◇ X2))) = X3 := superpose eq183 eq108
  have eq201 (X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq183 eq179
  have eq209 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq201 eq13
  have eq230 (X1 X2 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq183 eq209
  have eq235 (X1 X3 X4 : G) : ((X4 ◇ X3) ◇ (X3 ◇ X3)) = (X1 ◇ (X3 ◇ X3)) := superpose eq230 eq57
  have eq245 (X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = X3 := superpose eq230 eq235
  have eq248 (X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X2) = X3 := superpose eq245 eq194
  have eq251 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = X3 := superpose eq245 eq248
  have eq291 (X0 X3 : G) : X0 = X3 := superpose eq251 eq251
  have eq296 (X0 : G) : sK0 ≠ X0 := superpose eq291 eq8
  subsumption eq296 eq291


@[equational_result]
theorem Equation27316_implies_Equation2 (G : Type*) [Magma G] (h : Equation27316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq11
  have eq23 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq13 eq7
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq23 eq23
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq11 eq27
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq80 eq30


@[equational_result]
theorem Equation27318_implies_Equation2 (G : Type*) [Magma G] (h : Equation27318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27319_implies_Equation2 (G : Type*) [Magma G] (h : Equation27319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27320_implies_Equation2 (G : Type*) [Magma G] (h : Equation27320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27322_implies_Equation2 (G : Type*) [Magma G] (h : Equation27322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27323_implies_Equation2 (G : Type*) [Magma G] (h : Equation27323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27324_implies_Equation2 (G : Type*) [Magma G] (h : Equation27324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27326_implies_Equation2 (G : Type*) [Magma G] (h : Equation27326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27327_implies_Equation2 (G : Type*) [Magma G] (h : Equation27327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27328_implies_Equation2 (G : Type*) [Magma G] (h : Equation27328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27329_implies_Equation2 (G : Type*) [Magma G] (h : Equation27329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27331_implies_Equation2 (G : Type*) [Magma G] (h : Equation27331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X2 ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq11
  have eq14 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X2)))) = X4 := superpose eq11 eq11
  have eq23 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq14 eq13
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq144 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq144 eq49


@[equational_result]
theorem Equation27332_implies_Equation2 (G : Type*) [Magma G] (h : Equation27332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) ◇ X0) ◇ (X5 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4)))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ (X1 ◇ X3)) := superpose eq7 eq11
  have eq47 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq13 eq13
  have eq54 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X3)) = X1 := superpose eq47 eq15
  have eq56 (X0 X1 X3 X5 : G) : (((X1 ◇ X3) ◇ X0) ◇ (X5 ◇ X3)) = X5 := superpose eq54 eq10
  have eq66 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq11 eq56
  have eq76 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = X3 := superpose eq66 eq11
  have eq88 (X0 X3 : G) : X0 = X3 := superpose eq56 eq76
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq102 eq88


@[equational_result]
theorem Equation27333_implies_Equation2 (G : Type*) [Magma G] (h : Equation27333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X3) ◇ X4)) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq11 eq11
  have eq17 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq7
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq9
  have eq38 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X3 ◇ ((X3 ◇ X4) ◇ X2)) := superpose eq9 eq11
  have eq41 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X2 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq9 eq17
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq17 eq17
  have eq53 (X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X3) ◇ X1)) = X1 := superpose eq42 eq41
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq53 eq38
  have eq63 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq56 eq16
  have eq65 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq63 eq24
  have eq82 (X0 X3 X4 : G) : (X0 ◇ (X0 ◇ X3)) = X4 := superpose eq63 eq65
  have eq83 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq63 eq82
  have eq84 (X0 X3 : G) : X0 = X3 := superpose eq83 eq83
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq89 eq84


@[equational_result]
theorem Equation27334_implies_Equation2 (G : Type*) [Magma G] (h : Equation27334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X4 : G) : (X2 ◇ (X0 ◇ X4)) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq14
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation27336_implies_Equation2 (G : Type*) [Magma G] (h : Equation27336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27337_implies_Equation2 (G : Type*) [Magma G] (h : Equation27337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27338_implies_Equation2 (G : Type*) [Magma G] (h : Equation27338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27339_implies_Equation2 (G : Type*) [Magma G] (h : Equation27339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27341_implies_Equation2 (G : Type*) [Magma G] (h : Equation27341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27342_implies_Equation2 (G : Type*) [Magma G] (h : Equation27342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27343_implies_Equation2 (G : Type*) [Magma G] (h : Equation27343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27344_implies_Equation2 (G : Type*) [Magma G] (h : Equation27344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27346_implies_Equation2 (G : Type*) [Magma G] (h : Equation27346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27347_implies_Equation2 (G : Type*) [Magma G] (h : Equation27347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27348_implies_Equation2 (G : Type*) [Magma G] (h : Equation27348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27349_implies_Equation2 (G : Type*) [Magma G] (h : Equation27349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27351_implies_Equation2 (G : Type*) [Magma G] (h : Equation27351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27352_implies_Equation2 (G : Type*) [Magma G] (h : Equation27352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27353_implies_Equation2 (G : Type*) [Magma G] (h : Equation27353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27354_implies_Equation2 (G : Type*) [Magma G] (h : Equation27354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27355_implies_Equation2 (G : Type*) [Magma G] (h : Equation27355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27357_implies_Equation2 (G : Type*) [Magma G] (h : Equation27357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq14 eq11
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq24 eq14
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq48 eq29


@[equational_result]
theorem Equation27358_implies_Equation2 (G : Type*) [Magma G] (h : Equation27358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ (X5 ◇ (X0 ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ X4) = (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X4) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq11
  have eq24 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq16 eq10
  have eq26 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ (X5 ◇ X0)) = X5 := superpose eq24 eq9
  have eq30 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X5) = X5 := superpose eq24 eq26
  have eq31 (X0 X5 : G) : (X0 ◇ X5) = X5 := superpose eq24 eq30
  have eq34 (X0 X1 : G) : X0 = X1 := superpose eq24 eq31
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq36 eq34


@[equational_result]
theorem Equation27359_implies_Equation2 (G : Type*) [Magma G] (h : Equation27359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X2 ◇ (X1 ◇ X0)) := superpose eq9 eq11
  have eq33 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X1 := superpose eq14 eq31
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq14 eq33
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq44 eq40


@[equational_result]
theorem Equation27360_implies_Equation2 (G : Type*) [Magma G] (h : Equation27360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq84 eq33


@[equational_result]
theorem Equation27362_implies_Equation2 (G : Type*) [Magma G] (h : Equation27362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation27363_implies_Equation2 (G : Type*) [Magma G] (h : Equation27363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq11 eq11
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq115 eq38


@[equational_result]
theorem Equation27364_implies_Equation2 (G : Type*) [Magma G] (h : Equation27364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq64 eq19


@[equational_result]
theorem Equation27365_implies_Equation2 (G : Type*) [Magma G] (h : Equation27365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X5)) = X4 := superpose eq7 eq7
  have eq19 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation27367_implies_Equation2 (G : Type*) [Magma G] (h : Equation27367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ (X4 ◇ X5)) ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq11
  have eq23 (X0 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X0) = X5 := superpose eq13 eq12
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq11 eq23
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation27368_implies_Equation2 (G : Type*) [Magma G] (h : Equation27368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq54 eq16


@[equational_result]
theorem Equation27369_implies_Equation2 (G : Type*) [Magma G] (h : Equation27369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ ((X2 ◇ X3) ◇ X4)) = X5 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq11 eq9
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq41 eq33


@[equational_result]
theorem Equation27370_implies_Equation2 (G : Type*) [Magma G] (h : Equation27370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X5)) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27372_implies_Equation2 (G : Type*) [Magma G] (h : Equation27372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq39 eq19


@[equational_result]
theorem Equation27373_implies_Equation2 (G : Type*) [Magma G] (h : Equation27373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation27374_implies_Equation2 (G : Type*) [Magma G] (h : Equation27374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq31 eq13


@[equational_result]
theorem Equation27375_implies_Equation2 (G : Type*) [Magma G] (h : Equation27375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ X5)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27377_implies_Equation2 (G : Type*) [Magma G] (h : Equation27377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X0 ◇ (X5 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq38 eq18


@[equational_result]
theorem Equation27378_implies_Equation2 (G : Type*) [Magma G] (h : Equation27378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X5 : G) : (X0 ◇ (X5 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27379_implies_Equation2 (G : Type*) [Magma G] (h : Equation27379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X5 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27380_implies_Equation2 (G : Type*) [Magma G] (h : Equation27380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X5)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27381_implies_Equation2 (G : Type*) [Magma G] (h : Equation27381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X5 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27383_implies_Equation2 (G : Type*) [Magma G] (h : Equation27383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))) ◇ (X5 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X5 ◇ (X0 ◇ X1))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X4) ◇ (X5 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq43 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ X3) ◇ (X4 ◇ X0)) := superpose eq11 eq11
  have eq98 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (((X3 ◇ X0) ◇ X4) ◇ (X5 ◇ (X3 ◇ X0))) = (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X7) ◇ (X8 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) ◇ (X0 ◇ X6)) := superpose eq43 eq11
  have eq122 (X0 X1 X2 X3 X6 : G) : (X0 ◇ (X6 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))) = X6 := superpose eq7 eq9
  have eq163 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X1) ◇ (X6 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X5 ◇ X3)))))) = X6 := superpose eq9 eq10
  have eq178 (X0 X3 X4 X5 X6 X8 : G) : (((X3 ◇ X0) ◇ X4) ◇ (X5 ◇ (X3 ◇ X0))) = (X8 ◇ (X0 ◇ X6)) := superpose eq122 eq98
  have eq193 (X0 X1 X2 X6 : G) : ((X0 ◇ X1) ◇ (X6 ◇ X2)) = X6 := superpose eq122 eq163
  have eq194 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq193 eq7
  have eq250 (X0 X1 X2 X5 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = X5 := superpose eq194 eq10
  have eq253 (X0 X3 X4 X6 X8 : G) : (((X3 ◇ X0) ◇ X4) ◇ X3) = (X8 ◇ (X0 ◇ X6)) := superpose eq194 eq178
  have eq260 (X0 X3 X4 : G) : (((X3 ◇ X0) ◇ X4) ◇ X3) = X0 := superpose eq194 eq253
  have eq262 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq260 eq250
  have eq266 (X0 X3 : G) : X0 = X3 := superpose eq262 eq262
  have eq296 (X0 : G) : sK0 ≠ X0 := superpose eq266 eq8
  subsumption eq296 eq266


@[equational_result]
theorem Equation27384_implies_Equation2 (G : Type*) [Magma G] (h : Equation27384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))) ◇ (X5 ◇ (X0 ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X5 ◇ X2)) = X5 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq32 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X6 ◇ (((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2))) ◇ (X5 ◇ X1)) ◇ X3))) = X6 := superpose eq7 eq9
  have eq38 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X3) ◇ (X6 ◇ X5)) = ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2)))) ◇ X0) := superpose eq7 eq9
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X3 ◇ ((X4 ◇ X2) ◇ (X5 ◇ X4)))) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq9 eq16
  have eq50 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq16 eq16
  have eq63 (X1 X2 X3 X4 X5 : G) : (X1 ◇ X2) = (X1 ◇ (X3 ◇ ((X4 ◇ X2) ◇ (X5 ◇ X4)))) := superpose eq50 eq49
  have eq73 (X0 X3 X5 X6 : G) : ((X5 ◇ X3) ◇ (X6 ◇ X5)) = ((X0 ◇ X3) ◇ X0) := superpose eq63 eq38
  have eq83 (X3 X5 X6 : G) : ((X5 ◇ X3) ◇ (X6 ◇ X5)) = X3 := superpose eq50 eq73
  have eq88 (X0 X1 X3 X5 X6 : G) : (X0 ◇ (X6 ◇ (((X1 ◇ X3) ◇ (X5 ◇ X1)) ◇ X3))) = X6 := superpose eq83 eq32
  have eq90 (X1 X2 X3 : G) : (X1 ◇ X2) = (X1 ◇ (X3 ◇ X2)) := superpose eq83 eq63
  have eq100 (X0 X3 X6 : G) : (X0 ◇ (X6 ◇ (X3 ◇ X3))) = X6 := superpose eq83 eq88
  have eq102 (X0 X3 X6 : G) : (X0 ◇ (X6 ◇ X3)) = X6 := superpose eq90 eq100
  have eq120 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq16 eq102
  have eq123 (X0 X2 : G) : X0 = X2 := superpose eq16 eq120
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq123 eq8
  subsumption eq152 eq123


@[equational_result]
theorem Equation27385_implies_Equation2 (G : Type*) [Magma G] (h : Equation27385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X5 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X3)))) = X5 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq18 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ X2)) = X1 := superpose eq14 eq13
  have eq20 (X0 X1 X2 X5 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X5 ◇ X1)) = X5 := superpose eq18 eq10
  have eq21 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X3)) ◇ (X5 ◇ X4)) = X5 := superpose eq18 eq9
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) = X2 := superpose eq11 eq21
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) = (X4 ◇ (X2 ◇ X5)) := superpose eq21 eq21
  have eq32 (X2 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = X2 := superpose eq29 eq30
  have eq44 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1) ◇ X0) = X2 := superpose eq11 eq20
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq20
  have eq51 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ X0) = X2 := superpose eq32 eq44
  have eq53 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X0) = X2 := superpose eq47 eq51
  have eq54 (X0 X1 X5 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X5 ◇ X1)) = X5 := superpose eq47 eq20
  have eq62 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq47 eq53
  have eq63 (X0 X1 X5 : G) : (((X0 ◇ X1) ◇ X0) ◇ X5) = X5 := superpose eq47 eq54
  have eq64 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ X5) = X5 := superpose eq47 eq63
  have eq65 (X0 X5 : G) : (X0 ◇ X5) = X5 := superpose eq47 eq64
  have eq70 (X0 X1 : G) : X0 = X1 := superpose eq65 eq62
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq75 eq70


@[equational_result]
theorem Equation27386_implies_Equation2 (G : Type*) [Magma G] (h : Equation27386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq83 eq33


@[equational_result]
theorem Equation27388_implies_Equation2 (G : Type*) [Magma G] (h : Equation27388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27389_implies_Equation2 (G : Type*) [Magma G] (h : Equation27389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27390_implies_Equation2 (G : Type*) [Magma G] (h : Equation27390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27391_implies_Equation2 (G : Type*) [Magma G] (h : Equation27391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27393_implies_Equation2 (G : Type*) [Magma G] (h : Equation27393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27394_implies_Equation2 (G : Type*) [Magma G] (h : Equation27394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27395_implies_Equation2 (G : Type*) [Magma G] (h : Equation27395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27396_implies_Equation2 (G : Type*) [Magma G] (h : Equation27396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27398_implies_Equation2 (G : Type*) [Magma G] (h : Equation27398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27399_implies_Equation2 (G : Type*) [Magma G] (h : Equation27399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27400_implies_Equation2 (G : Type*) [Magma G] (h : Equation27400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27401_implies_Equation2 (G : Type*) [Magma G] (h : Equation27401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27403_implies_Equation2 (G : Type*) [Magma G] (h : Equation27403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27404_implies_Equation2 (G : Type*) [Magma G] (h : Equation27404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27405_implies_Equation2 (G : Type*) [Magma G] (h : Equation27405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27406_implies_Equation2 (G : Type*) [Magma G] (h : Equation27406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27407_implies_Equation2 (G : Type*) [Magma G] (h : Equation27407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27409_implies_Equation2 (G : Type*) [Magma G] (h : Equation27409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) = X2 := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq13
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq63 eq37


@[equational_result]
theorem Equation27410_implies_Equation2 (G : Type*) [Magma G] (h : Equation27410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X0 ◇ X2))) ◇ (X5 ◇ (X0 ◇ X2))) = X5 := superpose eq7 eq7
  have eq12 (X0 X2 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ (X0 ◇ X2))) = X4 := superpose eq7 eq9
  have eq45 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq12 eq12
  have eq125 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1)) = X3 := superpose eq45 eq7
  have eq137 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X3 ◇ X2)) = X3 := superpose eq45 eq7
  have eq151 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X1)) = X3 := superpose eq137 eq125
  have eq190 (X0 X4 : G) : ((X0 ◇ X0) ◇ X0) = X4 := superpose eq151 eq12
  have eq200 (X0 X2 : G) : X0 = X2 := superpose eq190 eq190
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq200 eq8
  subsumption eq207 eq200


@[equational_result]
theorem Equation27411_implies_Equation2 (G : Type*) [Magma G] (h : Equation27411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ (X0 ◇ X3))) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X5 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X4)))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X3 ◇ X5)) = (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0) = (X4 ◇ (X3 ◇ (X4 ◇ X5))) := superpose eq9 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ (X5 ◇ ((X6 ◇ X7) ◇ ((X0 ◇ X4) ◇ X7)))) = X5 := superpose eq7 eq10
  have eq27 (X0 X5 X6 X7 X8 : G) : (X0 ◇ (X6 ◇ ((X7 ◇ X8) ◇ (X5 ◇ X8)))) = X6 := superpose eq10 eq10
  have eq38 (X0 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X5 := superpose eq10 eq7
  have eq50 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X2 ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq9 eq38
  have eq52 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq38 eq38
  have eq64 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X2 ◇ X3))) = X1 := superpose eq52 eq50
  have eq70 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0) = X3 := superpose eq64 eq18
  have eq78 (X3 X4 X5 : G) : ((X4 ◇ X5) ◇ (X3 ◇ X5)) = X3 := superpose eq70 eq11
  have eq83 (X0 X1 X4 X5 X6 X7 : G) : (((X1 ◇ X0) ◇ X4) ◇ (X5 ◇ ((X6 ◇ X7) ◇ ((X0 ◇ X4) ◇ X7)))) = X5 := superpose eq78 eq21
  have eq85 (X0 X5 X6 : G) : (X0 ◇ (X6 ◇ X5)) = X6 := superpose eq78 eq27
  have eq90 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ (X5 ◇ (X0 ◇ X4))) = X5 := superpose eq78 eq83
  have eq100 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ X0) = X5 := superpose eq85 eq90
  have eq120 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq78 eq38
  have eq123 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq52 eq120
  have eq124 (X0 X4 X5 : G) : (X4 ◇ X0) = X5 := superpose eq123 eq100
  have eq131 (X0 X3 : G) : X0 = X3 := superpose eq124 eq124
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq133 eq131


@[equational_result]
theorem Equation27412_implies_Equation2 (G : Type*) [Magma G] (h : Equation27412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq51 eq34


@[equational_result]
theorem Equation27414_implies_Equation2 (G : Type*) [Magma G] (h : Equation27414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27415_implies_Equation2 (G : Type*) [Magma G] (h : Equation27415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27416_implies_Equation2 (G : Type*) [Magma G] (h : Equation27416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27417_implies_Equation2 (G : Type*) [Magma G] (h : Equation27417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27419_implies_Equation2 (G : Type*) [Magma G] (h : Equation27419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27420_implies_Equation2 (G : Type*) [Magma G] (h : Equation27420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27421_implies_Equation2 (G : Type*) [Magma G] (h : Equation27421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27422_implies_Equation2 (G : Type*) [Magma G] (h : Equation27422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27424_implies_Equation2 (G : Type*) [Magma G] (h : Equation27424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27425_implies_Equation2 (G : Type*) [Magma G] (h : Equation27425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27426_implies_Equation2 (G : Type*) [Magma G] (h : Equation27426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27427_implies_Equation2 (G : Type*) [Magma G] (h : Equation27427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27429_implies_Equation2 (G : Type*) [Magma G] (h : Equation27429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27430_implies_Equation2 (G : Type*) [Magma G] (h : Equation27430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27431_implies_Equation2 (G : Type*) [Magma G] (h : Equation27431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27432_implies_Equation2 (G : Type*) [Magma G] (h : Equation27432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27433_implies_Equation2 (G : Type*) [Magma G] (h : Equation27433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27435_implies_Equation2 (G : Type*) [Magma G] (h : Equation27435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq25 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq14 eq11
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq25 eq25
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation27436_implies_Equation2 (G : Type*) [Magma G] (h : Equation27436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X4)) ◇ (X5 ◇ (X0 ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq11 eq10
  have eq15 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X4)) ◇ X0) = X5 := superpose eq13 eq9
  have eq17 (X0 X4 X5 : G) : (X4 ◇ X0) = X5 := superpose eq13 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq26 eq18


@[equational_result]
theorem Equation27437_implies_Equation2 (G : Type*) [Magma G] (h : Equation27437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((X0 ◇ (X4 ◇ X4)) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) = X2 := superpose eq10 eq9
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) = (X3 ◇ (X2 ◇ X2)) := superpose eq9 eq9
  have eq27 (X2 X3 : G) : (X3 ◇ (X2 ◇ X2)) = X2 := superpose eq24 eq25
  have eq33 (X0 X1 : G) : X0 = X1 := superpose eq13 eq27
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq37 eq33


@[equational_result]
theorem Equation27438_implies_Equation2 (G : Type*) [Magma G] (h : Equation27438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq51 eq34


@[equational_result]
theorem Equation27440_implies_Equation2 (G : Type*) [Magma G] (h : Equation27440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27441_implies_Equation2 (G : Type*) [Magma G] (h : Equation27441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27442_implies_Equation2 (G : Type*) [Magma G] (h : Equation27442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27443_implies_Equation2 (G : Type*) [Magma G] (h : Equation27443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27445_implies_Equation2 (G : Type*) [Magma G] (h : Equation27445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27446_implies_Equation2 (G : Type*) [Magma G] (h : Equation27446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27447_implies_Equation2 (G : Type*) [Magma G] (h : Equation27447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27448_implies_Equation2 (G : Type*) [Magma G] (h : Equation27448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27450_implies_Equation2 (G : Type*) [Magma G] (h : Equation27450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27451_implies_Equation2 (G : Type*) [Magma G] (h : Equation27451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27452_implies_Equation2 (G : Type*) [Magma G] (h : Equation27452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27453_implies_Equation2 (G : Type*) [Magma G] (h : Equation27453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27455_implies_Equation2 (G : Type*) [Magma G] (h : Equation27455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27456_implies_Equation2 (G : Type*) [Magma G] (h : Equation27456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27457_implies_Equation2 (G : Type*) [Magma G] (h : Equation27457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27458_implies_Equation2 (G : Type*) [Magma G] (h : Equation27458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27459_implies_Equation2 (G : Type*) [Magma G] (h : Equation27459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27461_implies_Equation2 (G : Type*) [Magma G] (h : Equation27461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X0 ◇ (X5 ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq25 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq14 eq11
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation27462_implies_Equation2 (G : Type*) [Magma G] (h : Equation27462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X5 ◇ (X3 ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq23 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq13 eq11
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation27463_implies_Equation2 (G : Type*) [Magma G] (h : Equation27463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ (X7 ◇ X5)) = X7 := superpose eq7 eq7
  have eq11 (X0 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) = X2 := superpose eq11 eq9
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) = (X4 ◇ (X2 ◇ X5)) := superpose eq9 eq9
  have eq32 (X2 X4 X5 : G) : (X4 ◇ (X2 ◇ X5)) = X2 := superpose eq29 eq30
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq14 eq32
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq44 eq40


@[equational_result]
theorem Equation27464_implies_Equation2 (G : Type*) [Magma G] (h : Equation27464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 X7 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X7 ◇ (X0 ◇ X6))) = X7 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X7 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X7 := superpose eq11 eq10
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq31 eq24


@[equational_result]
theorem Equation27465_implies_Equation2 (G : Type*) [Magma G] (h : Equation27465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X0 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq78 eq24


@[equational_result]
theorem Equation27467_implies_Equation2 (G : Type*) [Magma G] (h : Equation27467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27468_implies_Equation2 (G : Type*) [Magma G] (h : Equation27468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27469_implies_Equation2 (G : Type*) [Magma G] (h : Equation27469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27470_implies_Equation2 (G : Type*) [Magma G] (h : Equation27470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27471_implies_Equation2 (G : Type*) [Magma G] (h : Equation27471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X1 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27473_implies_Equation2 (G : Type*) [Magma G] (h : Equation27473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27474_implies_Equation2 (G : Type*) [Magma G] (h : Equation27474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27475_implies_Equation2 (G : Type*) [Magma G] (h : Equation27475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27476_implies_Equation2 (G : Type*) [Magma G] (h : Equation27476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27477_implies_Equation2 (G : Type*) [Magma G] (h : Equation27477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X2 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27479_implies_Equation2 (G : Type*) [Magma G] (h : Equation27479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27480_implies_Equation2 (G : Type*) [Magma G] (h : Equation27480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27481_implies_Equation2 (G : Type*) [Magma G] (h : Equation27481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27482_implies_Equation2 (G : Type*) [Magma G] (h : Equation27482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27483_implies_Equation2 (G : Type*) [Magma G] (h : Equation27483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27485_implies_Equation2 (G : Type*) [Magma G] (h : Equation27485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


