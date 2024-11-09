import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation23814_implies_Equation2 (G : Type*) [Magma G] (h : Equation23814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23815_implies_Equation2 (G : Type*) [Magma G] (h : Equation23815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23816_implies_Equation2 (G : Type*) [Magma G] (h : Equation23816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23818_implies_Equation2 (G : Type*) [Magma G] (h : Equation23818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23819_implies_Equation2 (G : Type*) [Magma G] (h : Equation23819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23820_implies_Equation2 (G : Type*) [Magma G] (h : Equation23820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23821_implies_Equation2 (G : Type*) [Magma G] (h : Equation23821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23823_implies_Equation2 (G : Type*) [Magma G] (h : Equation23823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq56 eq22


@[equational_result]
theorem Equation23824_implies_Equation2 (G : Type*) [Magma G] (h : Equation23824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation23825_implies_Equation2 (G : Type*) [Magma G] (h : Equation23825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X3))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq10
  have eq25 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq16 eq10
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation23826_implies_Equation2 (G : Type*) [Magma G] (h : Equation23826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq30 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq50 eq30


@[equational_result]
theorem Equation23828_implies_Equation2 (G : Type*) [Magma G] (h : Equation23828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23829_implies_Equation2 (G : Type*) [Magma G] (h : Equation23829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23830_implies_Equation2 (G : Type*) [Magma G] (h : Equation23830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23831_implies_Equation2 (G : Type*) [Magma G] (h : Equation23831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23833_implies_Equation2 (G : Type*) [Magma G] (h : Equation23833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23834_implies_Equation2 (G : Type*) [Magma G] (h : Equation23834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23835_implies_Equation2 (G : Type*) [Magma G] (h : Equation23835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23836_implies_Equation2 (G : Type*) [Magma G] (h : Equation23836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23838_implies_Equation2 (G : Type*) [Magma G] (h : Equation23838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23839_implies_Equation2 (G : Type*) [Magma G] (h : Equation23839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23840_implies_Equation2 (G : Type*) [Magma G] (h : Equation23840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23841_implies_Equation2 (G : Type*) [Magma G] (h : Equation23841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23843_implies_Equation2 (G : Type*) [Magma G] (h : Equation23843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23844_implies_Equation2 (G : Type*) [Magma G] (h : Equation23844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23845_implies_Equation2 (G : Type*) [Magma G] (h : Equation23845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23846_implies_Equation2 (G : Type*) [Magma G] (h : Equation23846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23847_implies_Equation2 (G : Type*) [Magma G] (h : Equation23847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23849_implies_Equation2 (G : Type*) [Magma G] (h : Equation23849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq24 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq16 eq13
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq24 eq16
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation23850_implies_Equation2 (G : Type*) [Magma G] (h : Equation23850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ (X5 ◇ (X0 ◇ (X0 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ X3))) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X0)) = X5 := superpose eq10 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq25 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq16 eq10
  have eq28 (X0 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = X5 := superpose eq25 eq13
  have eq31 (X0 X4 X5 : G) : (X4 ◇ X0) = X5 := superpose eq25 eq28
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation23851_implies_Equation2 (G : Type*) [Magma G] (h : Equation23851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ (X5 ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X3) = (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ (((X4 ◇ X5) ◇ X3) ◇ X0)) := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0)))) = X3 := superpose eq9 eq10
  have eq31 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq32 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq10
  have eq41 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq32 eq9
  have eq47 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq32 eq41
  have eq60 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = (((X4 ◇ X5) ◇ ((X6 ◇ X3) ◇ X0)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X6 ◇ X3))) := superpose eq9 eq11
  have eq63 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X0) = (((X3 ◇ X4) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) := superpose eq32 eq11
  have eq94 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X0) = (((X3 ◇ X4) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq47 eq63
  have eq95 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X0) = (((X3 ◇ X4) ◇ X0) ◇ X0) := superpose eq32 eq94
  have eq96 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq47 eq95
  have eq102 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq96 eq24
  have eq107 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = (((X4 ◇ X5) ◇ X0) ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X6 ◇ X3))) := superpose eq96 eq60
  have eq113 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = (((X4 ◇ X5) ◇ X0) ◇ (X6 ◇ X3)) := superpose eq96 eq107
  have eq114 (X0 X1 X2 X3 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ (X6 ◇ X3)) := superpose eq96 eq113
  have eq115 (X0 X3 X6 : G) : (X0 ◇ (X6 ◇ X3)) = X0 := superpose eq102 eq114
  have eq117 (X0 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ X0))) = X4 := superpose eq115 eq10
  have eq129 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq115 eq117
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq129 eq31
  have eq144 (X0 X2 : G) : X0 = X2 := superpose eq130 eq130
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq152 eq144


@[equational_result]
theorem Equation23852_implies_Equation2 (G : Type*) [Magma G] (h : Equation23852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq22 (X0 X5 : G) : (X0 ◇ X5) = X5 := superpose eq14 eq10
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq22 eq14
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq34 eq29


@[equational_result]
theorem Equation23854_implies_Equation2 (G : Type*) [Magma G] (h : Equation23854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq10
  have eq24 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = X4 := superpose eq15 eq10
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq41 eq28


@[equational_result]
theorem Equation23855_implies_Equation2 (G : Type*) [Magma G] (h : Equation23855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq33 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq22 eq13
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq10 eq33
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq55 eq37


@[equational_result]
theorem Equation23856_implies_Equation2 (G : Type*) [Magma G] (h : Equation23856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq38 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X4)) = (X2 ◇ (X0 ◇ X1)) := superpose eq7 eq10
  have eq40 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq10
  have eq50 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq40 eq38
  have eq60 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq50 eq7
  have eq80 (X0 X4 : G) : X0 = X4 := superpose eq60 eq60
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq85 eq80


@[equational_result]
theorem Equation23857_implies_Equation2 (G : Type*) [Magma G] (h : Equation23857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ ((X1 ◇ X2) ◇ X6))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq13
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq86 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq86 eq39


@[equational_result]
theorem Equation23859_implies_Equation2 (G : Type*) [Magma G] (h : Equation23859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq10
  have eq23 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq13 eq10
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation23860_implies_Equation2 (G : Type*) [Magma G] (h : Equation23860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ X3))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq24 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq16 eq10
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation23861_implies_Equation2 (G : Type*) [Magma G] (h : Equation23861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq10
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X2 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X5 ◇ (X2 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X3))))))) = X5 := superpose eq10 eq7
  have eq23 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X2 := superpose eq17 eq13
  have eq29 (X0 X2 X3 X5 : G) : (X0 ◇ (X5 ◇ (X2 ◇ X3))) = X5 := superpose eq23 eq22
  have eq30 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq29 eq10
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq7 eq30
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq47 eq34


@[equational_result]
theorem Equation23862_implies_Equation2 (G : Type*) [Magma G] (h : Equation23862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ (X3 ◇ X6))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq21 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq13 eq10
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation23864_implies_Equation2 (G : Type*) [Magma G] (h : Equation23864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X3)))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5) ◇ (X6 ◇ X1)) ◇ (X7 ◇ X0)) = X7 := superpose eq9 eq7
  have eq36 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq10
  have eq41 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = X2 := superpose eq10 eq10
  have eq52 (X0 X6 X7 : G) : (X6 ◇ (X7 ◇ X0)) = X7 := superpose eq36 eq25
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq52 eq41
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq71 eq71
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq88 eq72


@[equational_result]
theorem Equation23865_implies_Equation2 (G : Type*) [Magma G] (h : Equation23865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ (X4 ◇ (X0 ◇ (X3 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X3))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4))) = X1 := superpose eq10 eq10
  have eq41 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := superpose eq9 eq10
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq16 eq16
  have eq70 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X4))) = X1 := superpose eq45 eq18
  have eq80 (X0 X1 X2 X3 X5 : G) : (X2 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X3) ◇ X5))) := superpose eq45 eq41
  have eq87 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X1 := superpose eq45 eq70
  have eq88 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := superpose eq45 eq80
  have eq89 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq45 eq88
  have eq90 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq89 eq87
  have eq96 (X0 X3 : G) : X0 = X3 := superpose eq90 eq90
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq101 eq96


@[equational_result]
theorem Equation23866_implies_Equation2 (G : Type*) [Magma G] (h : Equation23866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ (X4 ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X3 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq10
  have eq23 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq10
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq9 eq22
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq23
  have eq38 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3)))) = X4 := superpose eq35 eq10
  have eq41 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) = X4 := superpose eq35 eq38
  have eq42 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X3)) = X4 := superpose eq30 eq41
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq42 eq42
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq66 eq48


@[equational_result]
theorem Equation23867_implies_Equation2 (G : Type*) [Magma G] (h : Equation23867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ (X6 ◇ (X5 ◇ X7))) = X6 := superpose eq7 eq7
  have eq10 (X0 X3 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X6))) = X5 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X6 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X6))) = X2 := superpose eq10 eq10
  have eq30 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq10
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq30 eq28
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq49 eq49
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq68 eq52


@[equational_result]
theorem Equation23869_implies_Equation2 (G : Type*) [Magma G] (h : Equation23869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X1 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq10
  have eq24 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq13 eq10
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq7 eq24
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation23870_implies_Equation2 (G : Type*) [Magma G] (h : Equation23870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ (X6 ◇ (X7 ◇ (X0 ◇ (X4 ◇ X2))))) = X6 := superpose eq7 eq7
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X3))) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ X7) = X6 := superpose eq10 eq9
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq46 eq17


@[equational_result]
theorem Equation23871_implies_Equation2 (G : Type*) [Magma G] (h : Equation23871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X0 ◇ (X4 ◇ X3))))) = X5 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq10 eq10
  have eq43 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq28 eq10
  have eq46 (X0 X5 : G) : X0 = X5 := superpose eq7 eq43
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq83 eq46


@[equational_result]
theorem Equation23872_implies_Equation2 (G : Type*) [Magma G] (h : Equation23872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X6))) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq21 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq14 eq10
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation23873_implies_Equation2 (G : Type*) [Magma G] (h : Equation23873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X6 X7 X8 : G) : (X0 ◇ (X6 ◇ (X7 ◇ X8))) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq21 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq13 eq10
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation23875_implies_Equation2 (G : Type*) [Magma G] (h : Equation23875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X4 ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq10
  have eq24 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq17 eq10
  have eq30 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) = X0 := superpose eq24 eq12
  have eq33 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X1) = X0 := superpose eq24 eq30
  have eq34 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq24 eq33
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq40 eq35


@[equational_result]
theorem Equation23876_implies_Equation2 (G : Type*) [Magma G] (h : Equation23876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X3) ◇ (X5 ◇ (X1 ◇ (X0 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X3))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X5 X6 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq10
  have eq23 (X0 X1 X4 X5 : G) : ((X0 ◇ X4) ◇ X1) = X5 := superpose eq13 eq9
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq51 eq29


@[equational_result]
theorem Equation23877_implies_Equation2 (G : Type*) [Magma G] (h : Equation23877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X0 ◇ X3)) ◇ X0) = X1 := superpose eq7 eq7
  have eq39 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq10
  have eq52 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq39 eq12
  have eq78 (X0 X2 : G) : X0 = X2 := superpose eq52 eq52
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq80 eq78


@[equational_result]
theorem Equation23878_implies_Equation2 (G : Type*) [Magma G] (h : Equation23878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X0) = X1 := superpose eq7 eq7
  have eq35 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq46 eq35


@[equational_result]
theorem Equation23880_implies_Equation2 (G : Type*) [Magma G] (h : Equation23880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23881_implies_Equation2 (G : Type*) [Magma G] (h : Equation23881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23882_implies_Equation2 (G : Type*) [Magma G] (h : Equation23882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23883_implies_Equation2 (G : Type*) [Magma G] (h : Equation23883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23885_implies_Equation2 (G : Type*) [Magma G] (h : Equation23885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23886_implies_Equation2 (G : Type*) [Magma G] (h : Equation23886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23887_implies_Equation2 (G : Type*) [Magma G] (h : Equation23887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23888_implies_Equation2 (G : Type*) [Magma G] (h : Equation23888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23890_implies_Equation2 (G : Type*) [Magma G] (h : Equation23890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23891_implies_Equation2 (G : Type*) [Magma G] (h : Equation23891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23892_implies_Equation2 (G : Type*) [Magma G] (h : Equation23892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23893_implies_Equation2 (G : Type*) [Magma G] (h : Equation23893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23895_implies_Equation2 (G : Type*) [Magma G] (h : Equation23895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23896_implies_Equation2 (G : Type*) [Magma G] (h : Equation23896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23897_implies_Equation2 (G : Type*) [Magma G] (h : Equation23897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23898_implies_Equation2 (G : Type*) [Magma G] (h : Equation23898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23899_implies_Equation2 (G : Type*) [Magma G] (h : Equation23899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23901_implies_Equation2 (G : Type*) [Magma G] (h : Equation23901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq10
  have eq23 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq13 eq10
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation23902_implies_Equation2 (G : Type*) [Magma G] (h : Equation23902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X3))) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq10
  have eq26 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq17 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation23903_implies_Equation2 (G : Type*) [Magma G] (h : Equation23903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X5 ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X2 ◇ (X0 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ (X5 ◇ (X3 ◇ (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X3))))))) = X5 := superpose eq10 eq7
  have eq39 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ X1) := superpose eq9 eq10
  have eq51 (X0 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ (X0 ◇ X3))) = X0 := superpose eq9 eq39
  have eq89 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq51 eq22
  have eq141 (X0 X4 : G) : X0 = X4 := superpose eq7 eq89
  have eq235 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq235 eq141


@[equational_result]
theorem Equation23904_implies_Equation2 (G : Type*) [Magma G] (h : Equation23904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) ◇ X0) = X3 := superpose eq7 eq7
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq43 eq33


@[equational_result]
theorem Equation23906_implies_Equation2 (G : Type*) [Magma G] (h : Equation23906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23907_implies_Equation2 (G : Type*) [Magma G] (h : Equation23907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23908_implies_Equation2 (G : Type*) [Magma G] (h : Equation23908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23909_implies_Equation2 (G : Type*) [Magma G] (h : Equation23909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23911_implies_Equation2 (G : Type*) [Magma G] (h : Equation23911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23912_implies_Equation2 (G : Type*) [Magma G] (h : Equation23912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23913_implies_Equation2 (G : Type*) [Magma G] (h : Equation23913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23914_implies_Equation2 (G : Type*) [Magma G] (h : Equation23914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23916_implies_Equation2 (G : Type*) [Magma G] (h : Equation23916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23917_implies_Equation2 (G : Type*) [Magma G] (h : Equation23917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23918_implies_Equation2 (G : Type*) [Magma G] (h : Equation23918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23919_implies_Equation2 (G : Type*) [Magma G] (h : Equation23919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23921_implies_Equation2 (G : Type*) [Magma G] (h : Equation23921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23922_implies_Equation2 (G : Type*) [Magma G] (h : Equation23922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23923_implies_Equation2 (G : Type*) [Magma G] (h : Equation23923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23924_implies_Equation2 (G : Type*) [Magma G] (h : Equation23924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23925_implies_Equation2 (G : Type*) [Magma G] (h : Equation23925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23927_implies_Equation2 (G : Type*) [Magma G] (h : Equation23927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (X4 ◇ (X5 ◇ ((X1 ◇ X2) ◇ X3)))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X1)) = X4 := superpose eq9 eq9
  have eq27 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq22 eq10
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq27
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq55 eq29


@[equational_result]
theorem Equation23928_implies_Equation2 (G : Type*) [Magma G] (h : Equation23928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (X4 ◇ (X5 ◇ (X3 ◇ (X0 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X4 ◇ X3))) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X5)) ◇ X0)) = X3 := superpose eq10 eq10
  have eq40 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9
  have eq49 (X1 X3 X5 : G) : (X1 ◇ X5) = X3 := superpose eq40 eq18
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq49
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq122 eq60


@[equational_result]
theorem Equation23929_implies_Equation2 (G : Type*) [Magma G] (h : Equation23929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq33 (X0 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ X4)) = X5 := superpose eq12 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq110 eq47


@[equational_result]
theorem Equation23930_implies_Equation2 (G : Type*) [Magma G] (h : Equation23930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ (X5 ◇ (X6 ◇ X7))) = X6 := superpose eq7 eq7
  have eq10 (X0 X3 X4 X5 X6 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9
  have eq23 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq18 eq10
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation23932_implies_Equation2 (G : Type*) [Magma G] (h : Equation23932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23933_implies_Equation2 (G : Type*) [Magma G] (h : Equation23933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23934_implies_Equation2 (G : Type*) [Magma G] (h : Equation23934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23935_implies_Equation2 (G : Type*) [Magma G] (h : Equation23935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23937_implies_Equation2 (G : Type*) [Magma G] (h : Equation23937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23938_implies_Equation2 (G : Type*) [Magma G] (h : Equation23938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23939_implies_Equation2 (G : Type*) [Magma G] (h : Equation23939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23940_implies_Equation2 (G : Type*) [Magma G] (h : Equation23940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23942_implies_Equation2 (G : Type*) [Magma G] (h : Equation23942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23943_implies_Equation2 (G : Type*) [Magma G] (h : Equation23943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23944_implies_Equation2 (G : Type*) [Magma G] (h : Equation23944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23945_implies_Equation2 (G : Type*) [Magma G] (h : Equation23945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23947_implies_Equation2 (G : Type*) [Magma G] (h : Equation23947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23948_implies_Equation2 (G : Type*) [Magma G] (h : Equation23948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23949_implies_Equation2 (G : Type*) [Magma G] (h : Equation23949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23950_implies_Equation2 (G : Type*) [Magma G] (h : Equation23950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23951_implies_Equation2 (G : Type*) [Magma G] (h : Equation23951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23953_implies_Equation2 (G : Type*) [Magma G] (h : Equation23953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X1 ◇ X2)))) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq10
  have eq24 (X0 X1 X6 : G) : (X0 ◇ X1) = X6 := superpose eq13 eq10
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq7 eq24
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation23954_implies_Equation2 (G : Type*) [Magma G] (h : Equation23954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ (X6 ◇ (X7 ◇ (X4 ◇ (X0 ◇ X2))))) = X7 := superpose eq7 eq7
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X3))) = X6 := superpose eq7 eq7
  have eq13 (X0 X4 X5 X7 : G) : ((X0 ◇ X5) ◇ X4) = X7 := superpose eq10 eq9
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq46 eq17


@[equational_result]
theorem Equation23955_implies_Equation2 (G : Type*) [Magma G] (h : Equation23955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X6 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X6 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq53 eq35


@[equational_result]
theorem Equation23956_implies_Equation2 (G : Type*) [Magma G] (h : Equation23956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X5))) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation23957_implies_Equation2 (G : Type*) [Magma G] (h : Equation23957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X0 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X7 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X7 := superpose eq7 eq7
  have eq29 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation23959_implies_Equation2 (G : Type*) [Magma G] (h : Equation23959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23960_implies_Equation2 (G : Type*) [Magma G] (h : Equation23960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23961_implies_Equation2 (G : Type*) [Magma G] (h : Equation23961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23962_implies_Equation2 (G : Type*) [Magma G] (h : Equation23962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23963_implies_Equation2 (G : Type*) [Magma G] (h : Equation23963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X1 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23965_implies_Equation2 (G : Type*) [Magma G] (h : Equation23965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23966_implies_Equation2 (G : Type*) [Magma G] (h : Equation23966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23967_implies_Equation2 (G : Type*) [Magma G] (h : Equation23967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23968_implies_Equation2 (G : Type*) [Magma G] (h : Equation23968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23969_implies_Equation2 (G : Type*) [Magma G] (h : Equation23969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X2 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23971_implies_Equation2 (G : Type*) [Magma G] (h : Equation23971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23972_implies_Equation2 (G : Type*) [Magma G] (h : Equation23972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23973_implies_Equation2 (G : Type*) [Magma G] (h : Equation23973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23974_implies_Equation2 (G : Type*) [Magma G] (h : Equation23974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23975_implies_Equation2 (G : Type*) [Magma G] (h : Equation23975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X3 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23977_implies_Equation2 (G : Type*) [Magma G] (h : Equation23977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23978_implies_Equation2 (G : Type*) [Magma G] (h : Equation23978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23979_implies_Equation2 (G : Type*) [Magma G] (h : Equation23979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23980_implies_Equation2 (G : Type*) [Magma G] (h : Equation23980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23981_implies_Equation2 (G : Type*) [Magma G] (h : Equation23981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23983_implies_Equation2 (G : Type*) [Magma G] (h : Equation23983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X5 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23984_implies_Equation2 (G : Type*) [Magma G] (h : Equation23984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X5 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23985_implies_Equation2 (G : Type*) [Magma G] (h : Equation23985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X5 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23986_implies_Equation2 (G : Type*) [Magma G] (h : Equation23986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X5 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23987_implies_Equation2 (G : Type*) [Magma G] (h : Equation23987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X5 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23988_implies_Equation2 (G : Type*) [Magma G] (h : Equation23988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X5 ◇ X6))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24204_implies_Equation2 (G : Type*) [Magma G] (h : Equation24204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq10 eq10
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq10 eq10
  have eq16 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq7
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq12
  have eq20 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq18 eq16
  have eq22 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq10 eq9
  have eq33 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X3)) := superpose eq20 eq22
  have eq34 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq20 eq33
  have eq40 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq34 eq7
  have eq49 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq34 eq40
  have eq50 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq34 eq49
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq50 eq50
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq58 eq56


@[equational_result]
theorem Equation24207_implies_Equation2 (G : Type*) [Magma G] (h : Equation24207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : (((((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X0)) ◇ X3)) := superpose eq11 eq7
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) := superpose eq13 eq10
  have eq25 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq19 eq19
  have eq29 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq19 eq7
  have eq33 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) := superpose eq25 eq29
  have eq34 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) := superpose eq19 eq33
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X2) := superpose eq19 eq34
  have eq40 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) ◇ X3)) := superpose eq35 eq18
  have eq44 (X0 X1 X2 : G) : ((((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq35 eq15
  have eq46 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X3)) := superpose eq35 eq40
  have eq47 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) := superpose eq7 eq46
  have eq50 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X2 := superpose eq35 eq44
  have eq51 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X2 := superpose eq47 eq50
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq51 eq51
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq92 eq59


@[equational_result]
theorem Equation24209_implies_Equation2 (G : Type*) [Magma G] (h : Equation24209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X3) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0))) := superpose eq11 eq11
  have eq16 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose eq11 eq7
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = (X0 ◇ ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq7 eq9
  have eq51 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq11 eq12
  have eq60 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq18 eq51
  have eq77 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = (((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))))) := superpose eq10 eq12
  have eq79 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq10 eq9
  have eq80 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq10 eq11
  have eq87 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = (((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq10 eq77
  have eq88 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq7 eq79
  have eq89 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq10 eq80
  have eq90 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq7 eq88
  have eq129 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq7 eq16
  have eq163 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0) := superpose eq10 eq129
  have eq169 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq129 eq12
  have eq170 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq129 eq9
  have eq171 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq129 eq11
  have eq172 (X0 X1 : G) : (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq129 eq7
  have eq189 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq10 eq163
  have eq190 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq189 eq89
  have eq192 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq172 eq170
  have eq193 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq172 eq169
  have eq194 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq193 eq192
  have eq195 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq193 eq172
  have eq203 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = (((((X0 ◇ (X0 ◇ X0)) ◇ X3) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X3) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq194 eq87
  have eq204 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq194 eq88
  have eq209 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq194 eq190
  have eq210 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq194 eq189
  have eq220 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq210 eq203
  have eq280 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq195 eq11
  have eq287 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq195 eq280
  have eq291 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq195 eq204
  have eq300 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = X0 := superpose eq204 eq7
  have eq302 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X3) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0))) := superpose eq204 eq9
  have eq330 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq291 eq204
  have eq338 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq330 eq193
  have eq340 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq330 eq209
  have eq347 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq330 eq220
  have eq364 (X0 X1 X3 : G) : (X0 ◇ ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)))) = (X1 ◇ X1) := superpose eq330 eq24
  have eq416 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq330 eq338
  have eq418 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq330 eq340
  have eq434 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq330 eq347
  have eq435 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq171 eq434
  have eq436 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq416 eq435
  have eq437 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq330 eq436
  have eq438 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq418 eq437
  have eq439 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq330 eq438
  have eq440 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq439 eq287
  have eq442 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = (((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq439 eq60
  have eq443 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq439 eq195
  have eq449 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq440 eq90
  have eq450 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = (((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq440 eq442
  have eq451 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq443 eq439
  have eq452 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq451 eq450
  have eq453 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq451 eq449
  have eq462 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq451 eq330
  have eq467 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq451 eq452
  have eq468 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq451 eq453
  have eq470 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0))) := superpose eq468 eq13
  have eq472 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq468 eq467
  have eq473 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0)) := superpose eq468 eq470
  have eq516 (X0 X1 X3 : G) : (X0 ◇ ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq451 eq364
  have eq517 (X0 X1 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq472 eq516
  have eq650 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq462 eq300
  have eq651 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq462 eq650
  have eq652 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq451 eq651
  have eq659 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq472 eq302
  have eq660 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq462 eq659
  have eq661 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq451 eq660
  have eq662 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq462 eq661
  have eq663 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq662 eq472
  have eq667 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) := superpose eq663 eq473
  have eq670 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := superpose eq663 eq517
  have eq675 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq663 eq667
  have eq677 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq663 eq670
  have eq678 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq652 eq677
  have eq680 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq678 eq675
  have eq688 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq678 eq680
  have eq689 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq678 eq688
  have eq691 (X0 X1 : G) : X0 = X1 := superpose eq678 eq689
  have eq693 (X0 : G) : sK0 ≠ X0 := superpose eq691 eq8
  subsumption eq693 eq691


@[equational_result]
theorem Equation24210_implies_Equation2 (G : Type*) [Magma G] (h : Equation24210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq31 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq12
  have eq49 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq7 eq31
  have eq50 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq49 eq7
  have eq53 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X3))) = X2 := superpose eq49 eq11
  have eq70 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq49 eq50
  have eq76 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq70 eq53
  have eq77 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq70 eq76
  have eq78 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq70 eq77
  have eq82 (X0 X1 : G) : X0 = X1 := superpose eq70 eq78
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq87 eq82


@[equational_result]
theorem Equation24211_implies_Equation2 (G : Type*) [Magma G] (h : Equation24211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ (X0 ◇ X5)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq16 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq12 eq12
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq12
  have eq23 (X0 X2 X5 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X5)) = X2 := superpose eq14 eq11
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq23 eq17
  have eq26 (X2 X3 : G) : (X3 ◇ X2) = X3 := superpose eq25 eq14
  have eq32 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq26 eq16
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq26 eq32
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq54 eq44


@[equational_result]
theorem Equation24213_implies_Equation2 (G : Type*) [Magma G] (h : Equation24213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq11
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq11
  have eq22 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq16 eq14
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq7 eq10
  have eq53 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq22 eq7
  have eq56 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq22 eq7
  have eq60 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq22 eq53
  have eq61 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) := superpose eq60 eq27
  have eq73 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq22 eq9
  have eq120 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq60 eq9
  have eq136 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq60 eq120
  have eq137 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq22 eq136
  have eq139 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq137 eq73
  have eq140 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq137 eq56
  have eq174 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq140 eq139
  have eq176 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq140 eq174
  have eq178 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq176 eq61
  have eq186 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq176 eq178
  have eq253 (X0 X1 : G) : X0 = X1 := superpose eq186 eq176
  have eq255 (X0 : G) : sK0 ≠ X0 := superpose eq253 eq8
  subsumption eq255 eq253


@[equational_result]
theorem Equation24214_implies_Equation2 (G : Type*) [Magma G] (h : Equation24214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq11
  have eq15 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq11 eq7
  have eq19 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq15 eq12
  have eq21 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq15 eq19
  have eq52 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq21 eq21
  have eq54 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq21 eq11
  have eq62 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq21 eq54
  have eq68 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq62 eq52
  have eq70 (X0 X2 : G) : X0 = X2 := superpose eq68 eq68
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq78 eq70


@[equational_result]
theorem Equation24215_implies_Equation2 (G : Type*) [Magma G] (h : Equation24215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq7 eq11
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq15 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq11 eq7
  have eq20 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq15 eq12
  have eq22 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq15 eq20
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq14 eq22
  have eq33 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq29 eq22
  have eq34 (X0 X1 : G) : X0 = X1 := superpose eq14 eq33
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq39 eq34


@[equational_result]
theorem Equation24217_implies_Equation2 (G : Type*) [Magma G] (h : Equation24217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq32 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq7 eq11
  have eq49 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X3) ◇ X4) = X3 := superpose eq32 eq32
  have eq68 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq49 eq10
  have eq79 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X1) ◇ X1)) = X0 := superpose eq68 eq7
  have eq91 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq68 eq79
  have eq92 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq91 eq68
  have eq104 (X0 X1 : G) : X0 = X1 := superpose eq91 eq92
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq104 eq8
  subsumption eq118 eq104


@[equational_result]
theorem Equation24219_implies_Equation2 (G : Type*) [Magma G] (h : Equation24219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X4) ◇ (X0 ◇ X5)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X1 := superpose eq12 eq11
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq28 eq10
  have eq44 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq42 eq7
  have eq54 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq42 eq44
  have eq55 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X1 := superpose eq54 eq28
  have eq58 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq54 eq55
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq58 eq58
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq64 eq59


@[equational_result]
theorem Equation24221_implies_Equation2 (G : Type*) [Magma G] (h : Equation24221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq7 eq11
  have eq17 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq11 eq11
  have eq51 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq17 eq17
  have eq78 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq51 eq16
  have eq98 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq78 eq51
  have eq100 (X0 X3 : G) : X0 = X3 := superpose eq98 eq98
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq100 eq8
  subsumption eq119 eq100


@[equational_result]
theorem Equation24222_implies_Equation2 (G : Type*) [Magma G] (h : Equation24222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X2) = ((X0 ◇ ((X2 ◇ X2) ◇ X2)) ◇ ((X3 ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq10
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ X3) ◇ X3)) = X2 := superpose eq12 eq9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq13
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq12 eq15
  have eq20 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq16 eq15
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation24223_implies_Equation2 (G : Type*) [Magma G] (h : Equation24223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X3 ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq10
  have eq41 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq11 eq29
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq29 eq11
  have eq61 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq44 eq41
  have eq62 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq61 eq16
  have eq67 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq62 eq61
  have eq84 (X0 X1 : G) : X0 = X1 := superpose eq62 eq67
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq105 eq84


@[equational_result]
theorem Equation24225_implies_Equation2 (G : Type*) [Magma G] (h : Equation24225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X3) := superpose eq11 eq12
  have eq31 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq12 eq12
  have eq44 (X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X1))) = X1 := superpose eq31 eq10
  have eq54 (X1 X4 : G) : (X1 ◇ X4) = X1 := superpose eq31 eq44
  have eq55 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq54 eq30
  have eq57 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq54 eq55
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq57 eq57
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq63 eq58


@[equational_result]
theorem Equation24226_implies_Equation2 (G : Type*) [Magma G] (h : Equation24226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X4) ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X1 X3 X4 : G) : (X1 ◇ ((X3 ◇ X4) ◇ X3)) = X1 := superpose eq14 eq10
  have eq27 (X1 X4 : G) : (X1 ◇ X4) = X1 := superpose eq14 eq22
  have eq28 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq27 eq14
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq34 eq29


@[equational_result]
theorem Equation24227_implies_Equation2 (G : Type*) [Magma G] (h : Equation24227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ X3) = ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X4 ◇ X5) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X3 ◇ X4) ◇ X4)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq7 eq10
  have eq14 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ ((X4 ◇ X5) ◇ X5)) = X3 := superpose eq13 eq9
  have eq15 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X3)) = X0 := superpose eq13 eq7
  have eq16 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq13 eq14
  have eq17 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq13 eq15
  have eq18 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq17 eq16
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation24228_implies_Equation2 (G : Type*) [Magma G] (h : Equation24228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 X6 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ ((X4 ◇ X5) ◇ X6)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X1 X4 X5 X6 : G) : (X1 ◇ ((X4 ◇ X5) ◇ X6)) = X1 := superpose eq14 eq10
  have eq27 (X1 X5 : G) : (X1 ◇ X5) = X1 := superpose eq14 eq22
  have eq28 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq27 eq14
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq34 eq29


@[equational_result]
theorem Equation24231_implies_Equation2 (G : Type*) [Magma G] (h : Equation24231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq7 eq11
  have eq18 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq11
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3)) := superpose eq11 eq7
  have eq26 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq18
  have eq44 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq26 eq9
  have eq47 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq26 eq9
  have eq51 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq17 eq47
  have eq55 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq51 eq26
  have eq59 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq7 eq55
  have eq61 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq55 eq7
  have eq66 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq61 eq59
  have eq72 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3)) := superpose eq66 eq25
  have eq74 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq66 eq51
  have eq76 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq66 eq55
  have eq82 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq76 eq74
  have eq84 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq82 eq72
  have eq90 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq82 eq7
  have eq92 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) = X0 := superpose eq82 eq44
  have eq93 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq82 eq61
  have eq100 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq82 eq84
  have eq143 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = ((X0 ◇ ((X3 ◇ X0) ◇ X3)) ◇ (X0 ◇ X1)) := superpose eq100 eq100
  have eq144 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq82 eq100
  have eq150 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq92 eq143
  have eq161 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq150 eq144
  have eq162 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq93 eq161
  have eq163 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq162 eq90
  have eq173 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq162 eq163
  have eq174 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq82 eq173
  have eq197 (X0 X1 : G) : X0 = X1 := superpose eq174 eq162
  have eq225 (X0 : G) : sK0 ≠ X0 := superpose eq197 eq8
  subsumption eq225 eq197


@[equational_result]
theorem Equation24234_implies_Equation2 (G : Type*) [Magma G] (h : Equation24234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq11 eq11
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2)) = X1 := superpose eq11 eq7
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq7 eq9
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) = ((X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq26
  have eq49 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq26 eq11
  have eq59 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X2)) := superpose eq26 eq10
  have eq60 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X4)) := superpose eq7 eq10
  have eq70 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) = (((((((X2 ◇ X0) ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X1) ◇ X3)) ◇ X0) := superpose eq7 eq10
  have eq119 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((((((((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X1 ◇ X3)) := superpose eq10 eq13
  have eq154 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) = (((((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq15
  have eq179 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) = ((X0 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) ◇ ((((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) ◇ X3)) := superpose eq16 eq16
  have eq200 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) ◇ X1) = ((X1 ◇ ((((X2 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X1) ◇ ((X2 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)))) ◇ X0) := superpose eq16 eq26
  have eq204 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((((X1 ◇ X0) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3))) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3)))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq36
  have eq220 (X0 X1 X2 : G) : ((((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2))) = ((((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) := superpose eq36 eq36
  have eq222 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = (((((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) ◇ ((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X2)) ◇ (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq36 eq10
  have eq232 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq36 eq9
  have eq240 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = ((((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X2) := superpose eq36 eq11
  have eq249 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = ((((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2))) := superpose eq7 eq220
  have eq250 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X1 ◇ X3)) := superpose eq249 eq119
  have eq325 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = (((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq250 eq250
  have eq327 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq26 eq250
  have eq330 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) ◇ (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq36 eq250
  have eq331 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) = ((((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq7 eq250
  have eq345 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq250 eq12
  have eq346 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = (((((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) := superpose eq250 eq10
  have eq348 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq250 eq7
  have eq349 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X3)) := superpose eq250 eq7
  have eq350 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = ((((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) := superpose eq250 eq7
  have eq352 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X2))) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq250 eq9
  have eq358 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = ((((((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) := superpose eq250 eq12
  have eq363 (X0 X1 X2 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) = ((X2 ◇ (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq250 eq26
  have eq368 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq7 eq330
  have eq370 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq348 eq345
  have eq371 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) := superpose eq370 eq346
  have eq373 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = ((((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq371 eq325
  have eq375 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X3)) := superpose eq371 eq349
  have eq379 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) := superpose eq350 eq358
  have eq428 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = (((((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq250 eq70
  have eq457 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3))) = (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3))) ◇ X2) ◇ (X2 ◇ X4)) := superpose eq70 eq250
  have eq465 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq370 eq428
  have eq468 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (((((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ ((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X2)) ◇ (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq465 eq222
  have eq474 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq465 eq348
  have eq475 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq465 eq368
  have eq479 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq465 eq373
  have eq480 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X3)) := superpose eq465 eq375
  have eq518 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X3)) := superpose eq474 eq468
  have eq580 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) := superpose eq474 eq475
  have eq589 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq250 eq479
  have eq590 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) := superpose eq589 eq154
  have eq593 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) := superpose eq474 eq590
  have eq594 (X0 X1 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) = X0 := superpose eq7 eq593
  have eq597 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) := superpose eq480 eq379
  have eq598 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = ((X1 ◇ X2) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ (((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq480 eq352
  have eq608 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X2) ◇ ((((X1 ◇ X0) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3))) ◇ (X1 ◇ X2)) := superpose eq597 eq204
  have eq626 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X1 ◇ X2) ◇ ((((X1 ◇ X0) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3))) ◇ (X1 ◇ X2)) := superpose eq474 eq608
  have eq627 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X4)) := superpose eq626 eq60
  have eq633 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq580 eq627
  have eq695 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = ((X1 ◇ X2) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X1 ◇ X2))) ◇ X4)) := superpose eq597 eq598
  have eq696 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = ((X1 ◇ X2) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X4)) := superpose eq250 eq695
  have eq749 (X0 X1 X2 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) = (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) ◇ X2) ◇ (X2 ◇ X4)) := superpose eq633 eq457
  have eq750 (X0 X1 X2 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ (X2 ◇ X4)) := superpose eq580 eq749
  have eq751 (X0 X1 X2 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = (((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X2 ◇ X4)) := superpose eq331 eq750
  have eq776 (X0 X1 : G) : ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) = X0 := superpose eq594 eq7
  have eq822 (X0 X1 : G) : ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := superpose eq751 eq776
  have eq823 (X0 X1 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := superpose eq465 eq822
  have eq824 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq474 eq823
  have eq827 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = ((X2 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq824 eq363
  have eq829 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X1 := superpose eq824 eq465
  have eq832 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X3)) = X0 := superpose eq824 eq518
  have eq837 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq824 eq589
  have eq901 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X1 ◇ X2)) := superpose eq827 eq49
  have eq904 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)))) ◇ X2) := superpose eq827 eq240
  have eq905 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq901 eq327
  have eq937 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose eq837 eq905
  have eq952 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = (((X1 ◇ X2) ◇ X1) ◇ X2) := superpose eq937 eq904
  have eq957 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq937 eq59
  have eq962 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = X2 := superpose eq824 eq952
  have eq977 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2))) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X3)) := superpose eq962 eq232
  have eq986 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X3)) := superpose eq962 eq977
  have eq992 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose eq957 eq986
  have eq995 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq829 eq992
  have eq996 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2)) = X1 := superpose eq995 eq16
  have eq1000 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq995 eq179
  have eq1006 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X0) := superpose eq995 eq200
  have eq1026 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) := superpose eq1006 eq1000
  have eq1056 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq1026 eq996
  have eq1076 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq1056 eq594
  have eq1095 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (((X1 ◇ X0) ◇ X1) ◇ X3)) = X0 := superpose eq1076 eq832
  have eq1101 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) := superpose eq1076 eq696
  have eq1124 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X3)) = X0 := superpose eq1076 eq1095
  have eq1131 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = X1 := superpose eq1124 eq1101
  have eq1132 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq1076 eq1131
  have eq1137 (X0 X3 : G) : X0 = X3 := superpose eq1132 eq1132
  have eq1172 (X0 : G) : sK0 ≠ X0 := superpose eq1137 eq8
  subsumption eq1172 eq1137


@[equational_result]
theorem Equation24236_implies_Equation2 (G : Type*) [Magma G] (h : Equation24236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((((X0 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X3) ◇ (((X0 ◇ X2) ◇ X1) ◇ X3)) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) = (((((X0 ◇ X3) ◇ X2) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0) := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2))) := superpose eq10 eq7
  have eq38 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq7 eq14
  have eq78 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0) := superpose eq14 eq9
  have eq100 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq78 eq10
  have eq109 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)))) = X0 := superpose eq78 eq7
  have eq495 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)))) := superpose eq78 eq100
  have eq499 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq78 eq100
  have eq503 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq7 eq100
  have eq575 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq109 eq495
  have eq585 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq499 eq575
  have eq696 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq503 eq503
  have eq697 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq7 eq503
  have eq712 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)))) := superpose eq78 eq503
  have eq715 (X0 X1 : G) : (X0 ◇ X1) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq100 eq503
  have eq718 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq503 eq9
  have eq730 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq503 eq78
  have eq785 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq499 eq712
  have eq786 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq585 eq785
  have eq787 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq585 eq715
  have eq793 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq787 eq786
  have eq900 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) := superpose eq503 eq793
  have eq970 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq900 eq38
  have eq1018 (X0 X1 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq9 eq16
  have eq1100 (X0 X1 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq900 eq1018
  have eq1228 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X2))) = (((((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X2)))) ◇ (((X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X2))) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X2))))) := superpose eq12 eq20
  have eq1408 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq718 eq10
  have eq1417 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq718 eq696
  have eq1440 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq1408 eq970
  have eq1447 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq1408 eq1100
  have eq1448 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq793 eq1417
  have eq1456 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq1448 eq14
  have eq1498 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq1448 eq1440
  have eq1530 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq1498 eq1447
  have eq1545 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq7 eq1456
  have eq1557 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq1456
  have eq1606 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq1448 eq1545
  have eq1607 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq1606 eq1498
  have eq1609 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq1607 eq1530
  have eq1617 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq730 eq1609
  have eq1632 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq730 eq1557
  have eq1633 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq1632
  have eq1634 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1633 eq1448
  have eq1677 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq1634 eq1617
  have eq1850 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq1634 eq1677
  have eq1851 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq1850 eq503
  have eq1855 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) := superpose eq1850 eq900
  have eq1861 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X2))) = ((((X0 ◇ X2) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X2)))) ◇ (((X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X2))) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ X2))))) := superpose eq1850 eq1228
  have eq2076 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq1850 eq697
  have eq2113 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq1850 eq1851
  have eq2118 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq1850 eq1855
  have eq2131 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = ((((X0 ◇ X2) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) ◇ (((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))))) := superpose eq1850 eq1861
  have eq2132 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X0 ◇ X2) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2))) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)))) := superpose eq2118 eq2131
  have eq2133 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq2118 eq2132
  have eq2134 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1850 eq2133
  have eq2582 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq1850 eq2076
  have eq2583 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq2113 eq2582
  have eq2604 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ X0))) := superpose eq2583 eq2134
  have eq2818 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq2583 eq2604
  have eq2819 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X0 ◇ X2) ◇ X1) ◇ X0) ◇ X0) := superpose eq1634 eq2818
  have eq2820 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq2583 eq2819
  have eq2821 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq2583 eq2820
  have eq2822 (X0 X3 : G) : X0 = X3 := superpose eq2821 eq2821
  have eq2827 (X0 : G) : sK0 ≠ X0 := superpose eq2822 eq8
  subsumption eq2827 eq2822


@[equational_result]
theorem Equation24238_implies_Equation2 (G : Type*) [Magma G] (h : Equation24238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X5 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X4)) := superpose eq7 eq10
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X1) ◇ X0) ◇ (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X5)) := superpose eq10 eq7
  have eq36 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq15 eq15
  have eq54 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := superpose eq15 eq7
  have eq65 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq36
  have eq71 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) = (((X3 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X3) ◇ (X1 ◇ X4)) := superpose eq12 eq11
  have eq77 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) := superpose eq10 eq11
  have eq112 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq65 eq65
  have eq141 (X1 X2 X3 X4 : G) : (((X3 ◇ X2) ◇ X3) ◇ (X1 ◇ X4)) = X2 := superpose eq112 eq71
  have eq149 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X1 := superpose eq141 eq77
  have eq150 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X1 := superpose eq141 eq19
  have eq152 (X0 X1 X3 X4 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X4)) = X0 := superpose eq149 eq54
  have eq157 (X0 X1 X2 X5 : G) : ((X2 ◇ X0) ◇ X2) = ((X2 ◇ X1) ◇ (X0 ◇ X5)) := superpose eq152 eq11
  have eq295 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) = X0 := superpose eq157 eq150
  have eq336 (X0 X1 X5 : G) : (X1 ◇ X5) = X0 := superpose eq150 eq295
  have eq339 (X0 X3 : G) : X0 = X3 := superpose eq336 eq336
  have eq455 (X0 : G) : sK0 ≠ X0 := superpose eq339 eq8
  subsumption eq455 eq339


@[equational_result]
theorem Equation24241_implies_Equation2 (G : Type*) [Magma G] (h : Equation24241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) = X1 := superpose eq10 eq7
  have eq17 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) = ((((X2 ◇ X0) ◇ X2) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ X0) := superpose eq7 eq9
  have eq27 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9
  have eq34 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X3)) := superpose eq9 eq10
  have eq36 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq7 eq27
  have eq82 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) = (X0 ◇ X0) := superpose eq36 eq23
  have eq83 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) := superpose eq36 eq17
  have eq85 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X1 := superpose eq36 eq14
  have eq97 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X1) := superpose eq36 eq83
  have eq98 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X1 ◇ X3)) := superpose eq97 eq34
  have eq103 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X3)) := superpose eq82 eq98
  have eq104 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X1 ◇ X1) := superpose eq97 eq103
  have eq105 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ (X0 ◇ X3)) := superpose eq104 eq9
  have eq111 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq85 eq105
  have eq120 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq111 eq36
  have eq132 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq120 eq111
  have eq139 (X0 X3 : G) : X0 = X3 := superpose eq132 eq132
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq139 eq8
  subsumption eq141 eq139


@[equational_result]
theorem Equation24244_implies_Equation2 (G : Type*) [Magma G] (h : Equation24244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) = (((X1 ◇ X3) ◇ (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) ◇ (((X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) ◇ (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) ◇ X4)) := superpose eq10 eq9
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq9
  have eq43 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq27 eq7
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq27 eq10
  have eq49 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) = ((X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ (((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ X4)) := superpose eq27 eq9
  have eq54 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq27 eq7
  have eq71 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq7 eq48
  have eq78 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) = (((X1 ◇ X3) ◇ (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X4)) := superpose eq71 eq22
  have eq79 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = ((X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ (((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ X4)) := superpose eq71 eq49
  have eq82 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = ((X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ (X1 ◇ X4)) := superpose eq54 eq79
  have eq94 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq27 eq11
  have eq129 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq43 eq94
  have eq140 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) = (((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X4)) := superpose eq129 eq78
  have eq142 (X0 X1 X3 X4 : G) : ((X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ (X1 ◇ X4)) = X0 := superpose eq129 eq82
  have eq163 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) = (((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) ◇ X0) := superpose eq129 eq140
  have eq164 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ X2) := superpose eq71 eq163
  have eq165 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1)))) ◇ X0) = X1 := superpose eq129 eq164
  have eq167 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X4)) = X0 := superpose eq129 eq142
  have eq169 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq167 eq165
  have eq176 (X0 X3 : G) : X0 = X3 := superpose eq7 eq169
  have eq266 (X0 : G) : sK0 ≠ X0 := superpose eq176 eq8
  subsumption eq266 eq176


@[equational_result]
theorem Equation24246_implies_Equation2 (G : Type*) [Magma G] (h : Equation24246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X2) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq10
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq9 eq9
  have eq45 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq31
  have eq109 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ X0) = X2 := superpose eq45 eq15
  have eq115 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq109
  have eq127 (X0 X2 : G) : X0 = X2 := superpose eq7 eq115
  have eq144 (X0 : G) : sK0 ≠ X0 := superpose eq127 eq8
  subsumption eq144 eq127


@[equational_result]
theorem Equation24247_implies_Equation2 (G : Type*) [Magma G] (h : Equation24247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = ((((X1 ◇ X3) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X4) ◇ X4)) := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X3))) := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9
  have eq36 (X0 X1 X2 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X2) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq10
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq19 eq7
  have eq73 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) = X2 := superpose eq19 eq7
  have eq173 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) := superpose eq65 eq65
  have eq180 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X2) ◇ X0) := superpose eq65 eq65
  have eq185 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X2) = X0 := superpose eq19 eq65
  have eq198 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = ((((X0 ◇ X3) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4) ◇ X4)) := superpose eq65 eq9
  have eq202 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = ((((X0 ◇ X3) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X3) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X4))) := superpose eq65 eq17
  have eq205 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X3)) = ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) := superpose eq65 eq19
  have eq207 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq185 eq180
  have eq213 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq207 eq173
  have eq214 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq207 eq185
  have eq229 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) := superpose eq73 eq198
  have eq230 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq229 eq213
  have eq235 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = ((((X0 ◇ X3) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq229 eq202
  have eq236 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = ((((X0 ◇ X3) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) := superpose eq65 eq235
  have eq237 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = ((((X0 ◇ X3) ◇ X3) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq207 eq236
  have eq238 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ X0) := superpose eq230 eq237
  have eq302 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq19 eq214
  have eq341 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = X0 := superpose eq302 eq238
  have eq342 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X3)) = X0 := superpose eq341 eq205
  have eq344 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq342 eq207
  have eq346 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq344 eq214
  have eq362 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X3) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X4) ◇ X4)) := superpose eq346 eq14
  have eq507 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X3) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq346 eq362
  have eq508 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq346 eq507
  have eq509 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq346 eq508
  have eq510 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X0) = X2 := superpose eq509 eq36
  have eq513 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq509 eq510
  have eq514 (X0 X3 : G) : X0 = X3 := superpose eq513 eq513
  have eq516 (X0 : G) : sK0 ≠ X0 := superpose eq514 eq8
  subsumption eq516 eq514


@[equational_result]
theorem Equation24248_implies_Equation2 (G : Type*) [Magma G] (h : Equation24248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X5)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ X2) = X3 := superpose eq11 eq11
  have eq19 (X0 X1 X2 X5 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X5)) = X2 := superpose eq15 eq10
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq19 eq19
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq52 eq33


@[equational_result]
theorem Equation24250_implies_Equation2 (G : Type*) [Magma G] (h : Equation24250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq11 eq7
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq17 eq11
  have eq60 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq45 eq11
  have eq72 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq60
  have eq83 (X0 X2 : G) : X0 = X2 := superpose eq7 eq72
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq165 eq83


@[equational_result]
theorem Equation24252_implies_Equation2 (G : Type*) [Magma G] (h : Equation24252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq12 eq12
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq106 eq36


@[equational_result]
theorem Equation24254_implies_Equation2 (G : Type*) [Magma G] (h : Equation24254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) = X3 := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq10 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) ◇ ((X4 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)))) := superpose eq10 eq7
  have eq35 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9
  have eq66 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) = X1 := superpose eq35 eq7
  have eq96 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq66 eq17
  have eq98 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq66 eq96
  have eq100 (X0 X1 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose eq98 eq9
  have eq105 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X0) = X3 := superpose eq98 eq15
  have eq106 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ ((X4 ◇ ((X2 ◇ X0) ◇ X2)) ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq98 eq19
  have eq130 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq98 eq100
  have eq132 (X0 X2 X3 : G) : (X3 ◇ X2) = ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq98 eq106
  have eq133 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq130 eq132
  have eq134 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq133 eq105
  have eq140 (X0 X3 : G) : X0 = X3 := superpose eq134 eq134
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq140 eq8
  subsumption eq145 eq140


@[equational_result]
theorem Equation24255_implies_Equation2 (G : Type*) [Magma G] (h : Equation24255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq9 eq9
  have eq25 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) ◇ ((X4 ◇ X3) ◇ X4)) = X1 := superpose eq9 eq7
  have eq32 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) ◇ ((X1 ◇ X3) ◇ X1)) ◇ (X4 ◇ ((X3 ◇ X4) ◇ X3))) := superpose eq9 eq10
  have eq39 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) ◇ (X5 ◇ ((X4 ◇ X5) ◇ X4))) = X1 := superpose eq9 eq10
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1) = (((X4 ◇ ((X3 ◇ X4) ◇ X3)) ◇ (X0 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)))) ◇ ((X5 ◇ (X0 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)))) ◇ X5)) := superpose eq10 eq9
  have eq56 (X1 X3 X4 : G) : (X1 ◇ X3) = (X1 ◇ (X4 ◇ ((X3 ◇ X4) ◇ X3))) := superpose eq25 eq32
  have eq74 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1) = (((X4 ◇ ((X3 ◇ X4) ◇ X3)) ◇ (X0 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)))) ◇ ((X5 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X5)) := superpose eq56 eq52
  have eq75 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1) = (((X4 ◇ ((X3 ◇ X4) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X5 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X5)) := superpose eq56 eq74
  have eq105 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X4 ◇ ((X3 ◇ X4) ◇ X3))) = X1 := superpose eq23 eq10
  have eq108 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X3)) = X2 := superpose eq23 eq7
  have eq109 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))) = X3 := superpose eq23 eq7
  have eq139 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = (X1 ◇ (((X3 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) := superpose eq7 eq56
  have eq173 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq105 eq139
  have eq183 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ ((X3 ◇ X4) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X5 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X5)) = ((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X2)) ◇ X1) := superpose eq173 eq75
  have eq197 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ ((X4 ◇ X3) ◇ X4)) = X1 := superpose eq173 eq25
  have eq202 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X5 ◇ ((X4 ◇ X5) ◇ X4))) = X1 := superpose eq173 eq39
  have eq229 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X2)) ◇ X1) = (((X4 ◇ ((X3 ◇ X4) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X2)) ◇ ((X5 ◇ X2) ◇ X5)) := superpose eq173 eq183
  have eq230 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X2)) ◇ X1) = (((X4 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X2) ◇ ((X5 ◇ X2) ◇ X5)) := superpose eq173 eq229
  have eq231 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X2)) ◇ X1) = (((X4 ◇ X3) ◇ X2) ◇ ((X5 ◇ X2) ◇ X5)) := superpose eq173 eq230
  have eq248 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X4 ◇ X3) ◇ X4)) = X1 := superpose eq173 eq197
  have eq249 (X0 X1 X2 X3 : G) : ((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X2)) ◇ X1) = X3 := superpose eq248 eq231
  have eq258 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X5 ◇ X4)) = X1 := superpose eq173 eq202
  have eq259 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X5 ◇ X4)) = X1 := superpose eq173 eq258
  have eq263 (X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X1) = X3 := superpose eq259 eq109
  have eq264 (X1 X2 X3 : G) : (X1 ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X3)) = X2 := superpose eq259 eq108
  have eq282 (X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X2)) ◇ X1) = X3 := superpose eq263 eq249
  have eq288 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq282 eq264
  have eq289 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X2)) = X0 := superpose eq288 eq7
  have eq307 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq288 eq289
  have eq308 (X0 X3 : G) : X0 = X3 := superpose eq307 eq307
  have eq310 (X0 : G) : sK0 ≠ X0 := superpose eq308 eq8
  subsumption eq310 eq308


@[equational_result]
theorem Equation24256_implies_Equation2 (G : Type*) [Magma G] (h : Equation24256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq11 eq11
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq145 eq39


@[equational_result]
theorem Equation24258_implies_Equation2 (G : Type*) [Magma G] (h : Equation24258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq11
  have eq32 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq15
  have eq33 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq11 eq15
  have eq48 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) = X0 := superpose eq32 eq7
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = X0 := superpose eq33 eq48
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq33 eq51
  have eq67 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq33 eq66
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq67 eq67
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq70 eq68


@[equational_result]
theorem Equation24259_implies_Equation2 (G : Type*) [Magma G] (h : Equation24259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X0)) = X2 := superpose eq10 eq11
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq7 eq10
  have eq23 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq10 eq15
  have eq29 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq12 eq12
  have eq34 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq29 eq23
  have eq35 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) = X0 := superpose eq34 eq7
  have eq37 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := superpose eq34 eq10
  have eq49 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq34 eq35
  have eq52 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq34 eq37
  have eq53 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq34 eq52
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq53 eq49
  have eq58 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq53 eq55
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq58 eq58
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq61 eq59


@[equational_result]
theorem Equation24260_implies_Equation2 (G : Type*) [Magma G] (h : Equation24260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X0 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq51 (X0 X1 : G) : X0 = X1 := superpose eq7 eq20
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq154 eq51


@[equational_result]
theorem Equation24262_implies_Equation2 (G : Type*) [Magma G] (h : Equation24262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq11 eq11
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq7 eq12
  have eq44 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq32 eq18
  have eq57 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq32 eq44
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq57 eq57
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq71 eq60


@[equational_result]
theorem Equation24263_implies_Equation2 (G : Type*) [Magma G] (h : Equation24263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq12 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq130 eq53


@[equational_result]
theorem Equation24264_implies_Equation2 (G : Type*) [Magma G] (h : Equation24264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq12 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq133 eq53


@[equational_result]
theorem Equation24265_implies_Equation2 (G : Type*) [Magma G] (h : Equation24265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq12 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation24267_implies_Equation2 (G : Type*) [Magma G] (h : Equation24267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq10 eq10
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq7 eq16
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq130 eq59


@[equational_result]
theorem Equation24268_implies_Equation2 (G : Type*) [Magma G] (h : Equation24268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X3) ◇ ((((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2))) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X3) ◇ (X0 ◇ X3)) := superpose eq7 eq9
  have eq40 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq13 eq10
  have eq42 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq13 eq10
  have eq63 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq42 eq40
  have eq71 (X0 X2 : G) : X0 = X2 := superpose eq7 eq63
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq119 eq71


@[equational_result]
theorem Equation24269_implies_Equation2 (G : Type*) [Magma G] (h : Equation24269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ ((X2 ◇ X2) ◇ X4)) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq125 eq38


@[equational_result]
theorem Equation24271_implies_Equation2 (G : Type*) [Magma G] (h : Equation24271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) = X2 := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X1) ◇ X1)) = X2 := superpose eq10 eq7
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq19 eq14
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq21 eq12
  have eq32 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq21 eq24
  have eq33 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq32 eq21
  have eq35 (X0 X1 : G) : X0 = X1 := superpose eq32 eq33
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq45 eq35


@[equational_result]
theorem Equation24272_implies_Equation2 (G : Type*) [Magma G] (h : Equation24272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X3) ◇ (X1 ◇ X3)) := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X2) ◇ X5) ◇ (X3 ◇ X5)) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X4) := superpose eq13 eq13
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ (X2 ◇ X3)) = X0 := superpose eq7 eq13
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X2) ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X5)) := superpose eq13 eq13
  have eq34 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X4) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X4)) = X3 := superpose eq13 eq7
  have eq40 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X4) = X2 := superpose eq18 eq16
  have eq41 (X0 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ X4) = X2 := superpose eq40 eq22
  have eq47 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X4)) = X3 := superpose eq41 eq34
  have eq75 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)))) = X2 := superpose eq10 eq7
  have eq82 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq47 eq75
  have eq83 (X0 X2 : G) : X0 = X2 := superpose eq7 eq82
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq166 eq83


@[equational_result]
theorem Equation24273_implies_Equation2 (G : Type*) [Magma G] (h : Equation24273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq135 eq41


@[equational_result]
theorem Equation24276_implies_Equation2 (G : Type*) [Magma G] (h : Equation24276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ ((X0 ◇ X3) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0))) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)))) = X2 := superpose eq10 eq7
  have eq23 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq7 eq9
  have eq62 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) ◇ X2) := superpose eq23 eq11
  have eq81 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq62 eq9
  have eq86 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq62 eq10
  have eq109 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)))) = X2 := superpose eq81 eq16
  have eq117 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)))) = X2 := superpose eq81 eq109
  have eq119 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq81 eq86
  have eq121 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq119 eq117
  have eq155 (X0 X1 : G) : X0 = X1 := superpose eq7 eq121
  have eq271 (X0 : G) : sK0 ≠ X0 := superpose eq155 eq8
  subsumption eq271 eq155


@[equational_result]
theorem Equation24277_implies_Equation2 (G : Type*) [Magma G] (h : Equation24277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X5)) = X2 := superpose eq10 eq10
  have eq25 (X0 X2 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X2 := superpose eq16 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq40 eq29


@[equational_result]
theorem Equation24279_implies_Equation2 (G : Type*) [Magma G] (h : Equation24279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X2 ◇ X4) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3) ◇ X5) ◇ X0) = X3 := superpose eq10 eq7
  have eq24 (X0 X2 X3 X5 : G) : ((X2 ◇ X5) ◇ X0) = X3 := superpose eq17 eq20
  have eq66 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq150 eq66


@[equational_result]
theorem Equation24280_implies_Equation2 (G : Type*) [Magma G] (h : Equation24280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X4) ◇ ((X0 ◇ X3) ◇ X2))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) = X2 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (((X2 ◇ X4) ◇ X5) ◇ X0))) ◇ X0) = X2 := superpose eq10 eq7
  have eq26 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq16 eq22
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq7 eq26
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq129 eq52


@[equational_result]
theorem Equation24281_implies_Equation2 (G : Type*) [Magma G] (h : Equation24281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ ((X2 ◇ X4) ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) = X2 := superpose eq10 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq15
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq108 eq41


@[equational_result]
theorem Equation24282_implies_Equation2 (G : Type*) [Magma G] (h : Equation24282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ ((X2 ◇ X5) ◇ X6)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq7 eq17
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq129 eq39


@[equational_result]
theorem Equation24284_implies_Equation2 (G : Type*) [Magma G] (h : Equation24284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq9 eq7
  have eq46 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq15 eq15
  have eq89 (X0 X3 : G) : X0 = X3 := superpose eq7 eq46
  have eq217 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq217 eq89


@[equational_result]
theorem Equation24285_implies_Equation2 (G : Type*) [Magma G] (h : Equation24285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq48 eq11


@[equational_result]
theorem Equation24286_implies_Equation2 (G : Type*) [Magma G] (h : Equation24286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq9
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq118 eq36


@[equational_result]
theorem Equation24288_implies_Equation2 (G : Type*) [Magma G] (h : Equation24288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq42 eq18


@[equational_result]
theorem Equation24289_implies_Equation2 (G : Type*) [Magma G] (h : Equation24289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) = X2 := superpose eq11 eq11
  have eq25 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq18 eq12
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq7 eq25
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq52 eq28


@[equational_result]
theorem Equation24290_implies_Equation2 (G : Type*) [Magma G] (h : Equation24290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X2) = X4 := superpose eq12 eq12
  have eq24 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq14 eq12
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq7 eq24
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation24293_implies_Equation2 (G : Type*) [Magma G] (h : Equation24293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ X3) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq7 eq9
  have eq63 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ X0) := superpose eq7 eq25
  have eq145 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X3 := superpose eq63 eq10
  have eq147 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X0)) = X2 := superpose eq63 eq7
  have eq187 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq147 eq145
  have eq450 (X0 X2 : G) : X0 = X2 := superpose eq187 eq187
  have eq455 (X0 : G) : sK0 ≠ X0 := superpose eq450 eq8
  subsumption eq455 eq450


@[equational_result]
theorem Equation24294_implies_Equation2 (G : Type*) [Magma G] (h : Equation24294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X2) = X4 := superpose eq12 eq12
  have eq24 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq14 eq12
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq7 eq24
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation24296_implies_Equation2 (G : Type*) [Magma G] (h : Equation24296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X4) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation24297_implies_Equation2 (G : Type*) [Magma G] (h : Equation24297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X4) ◇ ((X1 ◇ X3) ◇ X2))) = X2 := superpose eq7 eq7
  have eq21 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq10
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq129 eq53


@[equational_result]
theorem Equation24298_implies_Equation2 (G : Type*) [Magma G] (h : Equation24298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X4) ◇ X4)) = X2 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq51 eq21


@[equational_result]
theorem Equation24299_implies_Equation2 (G : Type*) [Magma G] (h : Equation24299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X5) ◇ X6)) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq53 eq22


@[equational_result]
theorem Equation24302_implies_Equation2 (G : Type*) [Magma G] (h : Equation24302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X0 ◇ X3) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ ((X2 ◇ X0) ◇ X2))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq12
  have eq41 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq7 eq16
  have eq47 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq41 eq10
  have eq49 (X0 X3 : G) : ((X0 ◇ X3) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq41 eq9
  have eq59 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = X0 := superpose eq47 eq49
  have eq60 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq47 eq59
  have eq69 (X0 X2 : G) : X0 = X2 := superpose eq60 eq60
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq77 eq69


@[equational_result]
theorem Equation24303_implies_Equation2 (G : Type*) [Magma G] (h : Equation24303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ X0) ◇ X3) ◇ X2) ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq12 eq12
  have eq23 (X0 X2 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X2 := superpose eq16 eq10
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq46 eq28


@[equational_result]
theorem Equation24305_implies_Equation2 (G : Type*) [Magma G] (h : Equation24305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = ((X0 ◇ X3) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X2) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = ((X0 ◇ X3) ◇ ((X3 ◇ X1) ◇ X1)) := superpose eq10 eq7
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) ◇ X2) ◇ X2) = X0 := superpose eq10 eq9
  have eq46 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ ((X3 ◇ X1) ◇ X2)) ◇ ((X3 ◇ X1) ◇ X2))) = (((X1 ◇ X0) ◇ X3) ◇ X3) := superpose eq31 eq31
  have eq47 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X1 := superpose eq9 eq31
  have eq83 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1)) ◇ X0) = X3 := superpose eq7 eq11
  have eq126 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) = X3 := superpose eq47 eq7
  have eq166 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) := superpose eq10 eq22
  have eq200 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X0)) = ((((X0 ◇ X1) ◇ X1) ◇ (((((X0 ◇ X2) ◇ X1) ◇ X3) ◇ X0) ◇ X0)) ◇ X3) := superpose eq22 eq126
  have eq224 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ X0) ◇ X1) = X3 := superpose eq47 eq126
  have eq293 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) ◇ X1)) ◇ X1) := superpose eq83 eq83
  have eq303 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((((X2 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) ◇ X4) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0))) ◇ X4) = X3 := superpose eq83 eq126
  have eq324 (X1 X2 X3 X4 : G) : ((((X2 ◇ (((X2 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) ◇ X4)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X4) = X3 := superpose eq46 eq303
  have eq335 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ ((((X2 ◇ X3) ◇ ((X3 ◇ X4) ◇ X2)) ◇ X0) ◇ X4)) ◇ (X0 ◇ X1)) ◇ X5) ◇ X2) ◇ X1) = X5 := superpose eq224 eq224
  have eq359 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq83 eq224
  have eq364 (X0 X1 X2 X3 : G) : ((((X1 ◇ ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X1))) ◇ X3) ◇ X0) ◇ X0) = X3 := superpose eq224 eq126
  have eq405 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) = ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq359 eq166
  have eq421 (X1 X2 X3 X4 : G) : (((X2 ◇ ((X2 ◇ (((X2 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) ◇ X4)) ◇ X1)) ◇ X1) ◇ X4) = X3 := superpose eq359 eq324
  have eq492 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) = X0 := superpose eq17 eq10
  have eq580 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ X0) = X3 := superpose eq492 eq364
  have eq582 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X0)) = ((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3) := superpose eq580 eq200
  have eq794 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq580 eq582
  have eq795 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq794 eq405
  have eq918 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = X2 := superpose eq580 eq795
  have eq919 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq918 eq293
  have eq940 (X1 X2 X3 X4 : G) : (((X2 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1)) ◇ X1) ◇ X4) = X3 := superpose eq919 eq421
  have eq951 (X2 X3 X4 : G) : ((X2 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) = X3 := superpose eq919 eq940
  have eq952 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq951 eq919
  have eq953 (X1 X2 X5 : G) : (X2 ◇ X1) = X5 := superpose eq952 eq335
  have eq1008 (X0 X3 : G) : X0 = X3 := superpose eq953 eq953
  have eq1013 (X0 : G) : sK0 ≠ X0 := superpose eq1008 eq8
  subsumption eq1013 eq1008


@[equational_result]
theorem Equation24307_implies_Equation2 (G : Type*) [Magma G] (h : Equation24307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ X5)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X4 ◇ X3) ◇ X5)) = X2 := superpose eq7 eq12
  have eq23 (X0 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ X5)) = X4 := superpose eq15 eq11
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq51 eq29


@[equational_result]
theorem Equation24310_implies_Equation2 (G : Type*) [Magma G] (h : Equation24310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ ((((X2 ◇ X2) ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) ◇ ((X2 ◇ X2) ◇ X2))) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = X2 := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X2 := superpose eq12 eq7
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) = X2 := superpose eq12 eq17
  have eq25 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq12 eq24
  have eq63 (X0 X1 : G) : X0 = X1 := superpose eq7 eq25
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq127 eq63


@[equational_result]
theorem Equation24311_implies_Equation2 (G : Type*) [Magma G] (h : Equation24311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ X2) ◇ X3) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X4 ◇ X4) ◇ X5)) = X2 := superpose eq7 eq12
  have eq22 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X2 := superpose eq15 eq10
  have eq24 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq22 eq12
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation24313_implies_Equation2 (G : Type*) [Magma G] (h : Equation24313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X4) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X3 ◇ X0)) ◇ X0) = X4 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq10
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq21 eq12
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq30
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq57 eq44


@[equational_result]
theorem Equation24314_implies_Equation2 (G : Type*) [Magma G] (h : Equation24314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq12
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq19 eq7
  have eq35 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq19 eq26
  have eq57 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq59 eq57


@[equational_result]
theorem Equation24315_implies_Equation2 (G : Type*) [Magma G] (h : Equation24315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X4) ◇ X4)) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq61 eq18


@[equational_result]
theorem Equation24316_implies_Equation2 (G : Type*) [Magma G] (h : Equation24316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X5) ◇ X6)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq12 eq12
  have eq23 (X0 X2 X3 X6 : G) : (X0 ◇ (X3 ◇ X6)) = X2 := superpose eq16 eq10
  have eq28 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq50 eq28


@[equational_result]
theorem Equation24318_implies_Equation2 (G : Type*) [Magma G] (h : Equation24318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X4 ◇ X2) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq119 eq42


@[equational_result]
theorem Equation24319_implies_Equation2 (G : Type*) [Magma G] (h : Equation24319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2))) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq10
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq93 eq55


@[equational_result]
theorem Equation24320_implies_Equation2 (G : Type*) [Magma G] (h : Equation24320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ ((X4 ◇ X2) ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq10 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq37 eq29


@[equational_result]
theorem Equation24321_implies_Equation2 (G : Type*) [Magma G] (h : Equation24321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ X2) ◇ X6)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq10 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq37 eq29


@[equational_result]
theorem Equation24323_implies_Equation2 (G : Type*) [Magma G] (h : Equation24323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq56 eq21


@[equational_result]
theorem Equation24324_implies_Equation2 (G : Type*) [Magma G] (h : Equation24324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ X1) ◇ X2))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq41 (X0 X7 : G) : X0 = X7 := superpose eq12 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq55 eq41


@[equational_result]
theorem Equation24325_implies_Equation2 (G : Type*) [Magma G] (h : Equation24325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq74 eq19


@[equational_result]
theorem Equation24326_implies_Equation2 (G : Type*) [Magma G] (h : Equation24326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X7 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ (X0 ◇ X7)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X7 : G) : (X3 ◇ (X0 ◇ X7)) = X4 := superpose eq12 eq11
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq46 eq17


@[equational_result]
theorem Equation24328_implies_Equation2 (G : Type*) [Magma G] (h : Equation24328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X4) ◇ X7) = X6 := superpose eq12 eq12
  have eq24 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq14 eq12
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation24329_implies_Equation2 (G : Type*) [Magma G] (h : Equation24329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ ((X3 ◇ X2) ◇ X2)) ◇ ((X3 ◇ X2) ◇ X2))) = X2 := superpose eq7 eq7
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq60 eq45


@[equational_result]
theorem Equation24330_implies_Equation2 (G : Type*) [Magma G] (h : Equation24330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ ((X3 ◇ X2) ◇ X3)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq43 eq33


@[equational_result]
theorem Equation24331_implies_Equation2 (G : Type*) [Magma G] (h : Equation24331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ ((X3 ◇ X2) ◇ X4)) ◇ X6)) = X2 := superpose eq7 eq7
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq43 eq33


@[equational_result]
theorem Equation24333_implies_Equation2 (G : Type*) [Magma G] (h : Equation24333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X4 ◇ X4) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq51 eq21


@[equational_result]
theorem Equation24334_implies_Equation2 (G : Type*) [Magma G] (h : Equation24334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X4 ◇ X0))) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ X2))) = X2 := superpose eq11 eq11
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq16 eq12
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation24335_implies_Equation2 (G : Type*) [Magma G] (h : Equation24335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ ((X4 ◇ X4) ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation24336_implies_Equation2 (G : Type*) [Magma G] (h : Equation24336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ X5) ◇ X6)) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation24338_implies_Equation2 (G : Type*) [Magma G] (h : Equation24338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq53 eq22


@[equational_result]
theorem Equation24339_implies_Equation2 (G : Type*) [Magma G] (h : Equation24339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ ((X3 ◇ X4) ◇ X2))) = X2 := superpose eq7 eq7
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq46 eq35


@[equational_result]
theorem Equation24340_implies_Equation2 (G : Type*) [Magma G] (h : Equation24340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ X5)) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation24341_implies_Equation2 (G : Type*) [Magma G] (h : Equation24341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ X6)) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation24342_implies_Equation2 (G : Type*) [Magma G] (h : Equation24342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X6 X7 X8 : G) : (X0 ◇ ((X6 ◇ X7) ◇ X8)) = X2 := superpose eq7 eq7
  have eq19 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation24345_implies_Equation2 (G : Type*) [Magma G] (h : Equation24345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq7 eq9
  have eq18 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq18 eq15
  have eq30 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq12
  have eq39 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq23 eq30
  have eq55 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq39 eq23
  have eq59 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq18 eq23
  have eq63 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq23 eq18
  have eq64 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq55 eq63
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq64 eq59
  have eq71 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq64 eq66
  have eq72 (X0 X1 : G) : X0 = X1 := superpose eq39 eq71
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq80 eq72


@[equational_result]
theorem Equation24348_implies_Equation2 (G : Type*) [Magma G] (h : Equation24348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq7 eq12
  have eq16 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq12
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq16
  have eq27 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := superpose eq9 eq9
  have eq30 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq12
  have eq37 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq7 eq14
  have eq47 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq20 eq37
  have eq48 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq47 eq27
  have eq51 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq47 eq48
  have eq53 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq51 eq30
  have eq59 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq20 eq53
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq59 eq7
  have eq66 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq59 eq12
  have eq74 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq59 eq47
  have eq87 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq59 eq66
  have eq96 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq59 eq74
  have eq99 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq96 eq64
  have eq100 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq96 eq87
  have eq104 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq96 eq99
  have eq105 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq96 eq104
  have eq124 (X0 X1 : G) : X0 = X1 := superpose eq105 eq100
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq124 eq8
  subsumption eq129 eq124


@[equational_result]
theorem Equation24350_implies_Equation2 (G : Type*) [Magma G] (h : Equation24350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X0) = (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq18 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq9
  have eq19 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq9 eq7
  have eq30 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq11 eq11
  have eq34 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq11 eq9
  have eq57 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq18 eq12
  have eq68 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq22 eq57
  have eq69 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) = X1 := superpose eq68 eq9
  have eq74 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq68 eq19
  have eq86 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq69 eq30
  have eq89 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq68 eq74
  have eq91 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq89 eq86
  have eq103 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := superpose eq91 eq7
  have eq104 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0)) := superpose eq91 eq10
  have eq109 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq91 eq34
  have eq136 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq91 eq109
  have eq137 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq91 eq136
  have eq138 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq137 eq104
  have eq197 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq103 eq138
  have eq202 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq137 eq197
  have eq203 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = X0 := superpose eq202 eq103
  have eq219 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq202 eq203
  have eq220 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq202 eq219
  have eq242 (X0 X1 : G) : X0 = X1 := superpose eq220 eq202
  have eq255 (X0 : G) : sK0 ≠ X0 := superpose eq242 eq8
  subsumption eq255 eq242


@[equational_result]
theorem Equation24351_implies_Equation2 (G : Type*) [Magma G] (h : Equation24351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = (X0 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq9 eq10
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq9 eq12
  have eq37 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3))) = X0 := superpose eq12 eq9
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X2) ◇ X2))) := superpose eq11 eq11
  have eq66 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)))) := superpose eq11 eq10
  have eq74 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) := superpose eq37 eq58
  have eq88 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq25 eq66
  have eq89 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq74 eq88
  have eq94 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq74
  have eq99 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X2) ◇ X2))) := superpose eq10 eq74
  have eq121 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq94 eq15
  have eq123 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ X0) := superpose eq94 eq25
  have eq127 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq94 eq35
  have eq130 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq123 eq74
  have eq138 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq127 eq7
  have eq139 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq127 eq9
  have eq140 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) := superpose eq127 eq12
  have eq144 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq138 eq89
  have eq145 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq130 eq144
  have eq147 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq139 eq145
  have eq159 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq127 eq140
  have eq167 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X2)) := superpose eq159 eq99
  have eq168 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) := superpose eq127 eq167
  have eq169 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq147 eq168
  have eq170 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq169 eq159
  have eq172 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq170 eq121
  have eq178 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq170 eq172
  have eq179 (X0 X1 : G) : X0 = X1 := superpose eq147 eq178
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq179 eq8
  subsumption eq187 eq179


@[equational_result]
theorem Equation24352_implies_Equation2 (G : Type*) [Magma G] (h : Equation24352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9
  have eq25 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) := superpose eq18 eq10
  have eq30 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq18 eq25
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq30 eq18
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq32 eq32
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation24355_implies_Equation2 (G : Type*) [Magma G] (h : Equation24355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq7 eq12
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq12 eq12
  have eq18 (X0 X1 X2 : G) : ((((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq12 eq7
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq12 eq9
  have eq28 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) = ((X0 ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq9
  have eq29 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq34 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq27 eq15
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq34 eq27
  have eq38 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq34 eq18
  have eq41 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq13 eq28
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq29 eq41
  have eq45 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X1 := superpose eq29 eq9
  have eq50 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq45 eq35
  have eq51 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq50 eq38
  have eq61 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq29 eq51
  have eq63 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X2)) := superpose eq61 eq42
  have eq65 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq61 eq63
  have eq66 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq65 eq29
  have eq69 (X0 X1 : G) : X0 = X1 := superpose eq65 eq66
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq82 eq69


@[equational_result]
theorem Equation24358_implies_Equation2 (G : Type*) [Magma G] (h : Equation24358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X3)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq10 eq9
  have eq13 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq10 eq12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X2)) = X0 := superpose eq13 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq13 eq14
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24360_implies_Equation2 (G : Type*) [Magma G] (h : Equation24360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ (((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X3) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose eq9 eq9
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq9
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq10 eq10
  have eq33 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq10 eq7
  have eq41 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = ((((X1 ◇ X1) ◇ X0) ◇ X3) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq7 eq28
  have eq42 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X3) ◇ (X1 ◇ X0)) := superpose eq9 eq28
  have eq60 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := superpose eq28 eq7
  have eq79 (X0 X1 X3 : G) : (X0 ◇ (((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X3) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq41 eq13
  have eq84 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose eq41 eq79
  have eq91 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X3) ◇ X0)) := superpose eq42 eq33
  have eq97 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq42 eq84
  have eq105 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq60 eq91
  have eq159 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq105 eq28
  have eq165 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose eq159 eq14
  have eq168 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ X1)) := superpose eq159 eq97
  have eq181 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq105 eq165
  have eq185 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq105 eq168
  have eq193 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq181 eq181
  have eq197 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq193 eq185
  have eq214 (X0 X2 : G) : X0 = X2 := superpose eq197 eq197
  have eq232 (X0 : G) : sK0 ≠ X0 := superpose eq214 eq8
  subsumption eq232 eq214


@[equational_result]
theorem Equation24362_implies_Equation2 (G : Type*) [Magma G] (h : Equation24362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X5 : G) : (((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ X5)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X5 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X5)) = X2 := superpose eq7 eq11
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq13 eq12
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ X3) := superpose eq14 eq10
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq14 eq15
  have eq22 (X0 X1 : G) : X0 = X1 := superpose eq14 eq18
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq25 eq22


@[equational_result]
theorem Equation24364_implies_Equation2 (G : Type*) [Magma G] (h : Equation24364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq7 eq9
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X0 ◇ X1)) := superpose eq18 eq15
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) = X1 := superpose eq18 eq9
  have eq34 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq7 eq26
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq18
  have eq40 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq18 eq7
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq26
  have eq46 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq18 eq39
  have eq58 (X0 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ X0) = X0 := superpose eq34 eq34
  have eq72 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq46 eq26
  have eq81 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq26 eq24
  have eq101 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq40 eq24
  have eq112 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq46 eq101
  have eq113 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq46 eq112
  have eq114 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq113 eq72
  have eq118 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq114 eq81
  have eq119 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq46 eq118
  have eq120 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq119 eq58
  have eq139 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq120 eq43
  have eq145 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq120 eq139
  have eq179 (X0 X1 : G) : X0 = X1 := superpose eq120 eq145
  have eq192 (X0 : G) : sK0 ≠ X0 := superpose eq179 eq8
  subsumption eq192 eq179


@[equational_result]
theorem Equation24365_implies_Equation2 (G : Type*) [Magma G] (h : Equation24365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq9 eq10
  have eq26 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq9 eq10
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq23 eq26
  have eq45 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq16 eq16
  have eq55 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq45 eq31
  have eq67 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq55 eq16
  have eq71 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq67 eq55
  have eq74 (X0 X1 : G) : X0 = X1 := superpose eq71 eq67
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq87 eq74


@[equational_result]
theorem Equation24366_implies_Equation2 (G : Type*) [Magma G] (h : Equation24366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq7 eq12
  have eq15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq12
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq12 eq7
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq16 eq14
  have eq27 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq9
  have eq38 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq27 eq15
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq38 eq19
  have eq54 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq38 eq40
  have eq62 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq54 eq40
  have eq63 (X0 X1 : G) : X0 = X1 := superpose eq38 eq62
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq71 eq63


@[equational_result]
theorem Equation24368_implies_Equation2 (G : Type*) [Magma G] (h : Equation24368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq9
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq9 eq7
  have eq23 (X0 X1 X2 X3 : G) : ((((X2 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X3 ◇ (((X2 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1))) ◇ (((X2 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)))) = (X0 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq7 eq10
  have eq25 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq10
  have eq30 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq10 eq10
  have eq36 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X3 ◇ X1) ◇ X1)) := superpose eq10 eq7
  have eq42 (X0 X1 X2 : G) : ((X2 ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq9 eq18
  have eq43 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq18 eq18
  have eq54 (X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = ((X2 ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq43 eq42
  have eq55 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq54 eq20
  have eq61 (X0 X3 : G) : ((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq55 eq25
  have eq69 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq55 eq61
  have eq90 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq12 eq7
  have eq97 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X0 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq90 eq23
  have eq120 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq10 eq30
  have eq139 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) = X1 := superpose eq30 eq7
  have eq162 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq55 eq120
  have eq168 (X1 X2 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = X1 := superpose eq139 eq36
  have eq169 (X0 X3 : G) : (X0 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq168 eq162
  have eq172 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq168 eq69
  have eq174 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq169 eq18
  have eq181 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq169 eq97
  have eq198 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq172 eq174
  have eq200 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq172 eq181
  have eq203 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq200 eq198
  have eq233 (X0 X1 : G) : X0 = X1 := superpose eq200 eq203
  have eq235 (X0 : G) : sK0 ≠ X0 := superpose eq233 eq8
  subsumption eq235 eq233


@[equational_result]
theorem Equation24370_implies_Equation2 (G : Type*) [Magma G] (h : Equation24370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq12
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq12
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq15 eq14
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq19 eq12
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation24372_implies_Equation2 (G : Type*) [Magma G] (h : Equation24372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq11
  have eq29 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose eq7 eq9
  have eq34 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq9
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq9 eq11
  have eq50 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq9 eq34
  have eq51 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq34 eq34
  have eq57 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq34 eq7
  have eq66 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq51 eq50
  have eq67 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq66 eq37
  have eq72 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = X1 := superpose eq67 eq29
  have eq78 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = X1 := superpose eq57 eq72
  have eq79 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq78 eq10
  have eq80 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq79 eq17
  have eq94 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq80 eq34
  have eq102 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq80 eq94
  have eq104 (X0 X1 : G) : X0 = X1 := superpose eq80 eq102
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq104 eq8
  subsumption eq118 eq104


@[equational_result]
theorem Equation24373_implies_Equation2 (G : Type*) [Magma G] (h : Equation24373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq37 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X3) ◇ X3)) = X2 := superpose eq10 eq7
  have eq38 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X3 := superpose eq10 eq9
  have eq49 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ X3)) = X2 := superpose eq9 eq37
  have eq50 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X3 := superpose eq9 eq38
  have eq60 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq50 eq49
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq60 eq60
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq74 eq63


@[equational_result]
theorem Equation24374_implies_Equation2 (G : Type*) [Magma G] (h : Equation24374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ X3) ◇ X4)) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X3)) = X0 := superpose eq18 eq7
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq18 eq23
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation24376_implies_Equation2 (G : Type*) [Magma G] (h : Equation24376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) = X1 := superpose eq11 eq9
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq9
  have eq45 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) = X1 := superpose eq34 eq33
  have eq60 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq34 eq45
  have eq61 (X0 X3 : G) : X0 = X3 := superpose eq60 eq60
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq69 eq61


@[equational_result]
theorem Equation24377_implies_Equation2 (G : Type*) [Magma G] (h : Equation24377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ ((X3 ◇ X3) ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ X3) ◇ X0))) = X2 := superpose eq16 eq11
  have eq27 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X2 := superpose eq16 eq26
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq27 eq27
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation24378_implies_Equation2 (G : Type*) [Magma G] (h : Equation24378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ X0) ◇ ((X3 ◇ X4) ◇ X4)) := superpose eq7 eq7
  have eq42 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq9 eq10
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq42 eq42
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq156 eq73


@[equational_result]
theorem Equation24379_implies_Equation2 (G : Type*) [Magma G] (h : Equation24379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq12
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation24382_implies_Equation2 (G : Type*) [Magma G] (h : Equation24382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq31 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq10
  have eq48 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq31 eq10
  have eq51 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq31 eq7
  have eq52 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) := superpose eq31 eq9
  have eq54 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq31 eq10
  have eq55 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq48 eq31
  have eq62 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq51 eq52
  have eq70 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq62 eq55
  have eq79 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq51 eq54
  have eq80 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq62 eq79
  have eq81 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq80 eq51
  have eq85 (X0 X1 : G) : X0 = X1 := superpose eq70 eq81
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq113 eq85


@[equational_result]
theorem Equation24385_implies_Equation2 (G : Type*) [Magma G] (h : Equation24385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X0 := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq11 eq7
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq33 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq12 eq22
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq33 eq9
  have eq38 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq33 eq12
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq33 eq16
  have eq46 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ X0) := superpose eq38 eq41
  have eq47 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq33 eq46
  have eq49 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq47 eq36
  have eq53 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq47 eq49
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq53 eq53
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq56 eq54


@[equational_result]
theorem Equation24387_implies_Equation2 (G : Type*) [Magma G] (h : Equation24387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq21 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq7 eq10
  have eq54 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq110 eq54


@[equational_result]
theorem Equation24388_implies_Equation2 (G : Type*) [Magma G] (h : Equation24388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = (((X1 ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) := superpose eq7 eq9
  have eq18 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = X0 := superpose eq9 eq9
  have eq21 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq18 eq17
  have eq22 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq21 eq11
  have eq25 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X1 := superpose eq22 eq22
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq25
  have eq36 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ X2) = X0 := superpose eq35 eq7
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq35 eq36
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq45 eq45
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq48 eq46


@[equational_result]
theorem Equation24389_implies_Equation2 (G : Type*) [Magma G] (h : Equation24389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq60 (X0 X1 : G) : X0 = X1 := superpose eq7 eq18
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq122 eq60


@[equational_result]
theorem Equation24392_implies_Equation2 (G : Type*) [Magma G] (h : Equation24392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq37 eq15


@[equational_result]
theorem Equation24394_implies_Equation2 (G : Type*) [Magma G] (h : Equation24394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation24395_implies_Equation2 (G : Type*) [Magma G] (h : Equation24395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation24397_implies_Equation2 (G : Type*) [Magma G] (h : Equation24397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24398_implies_Equation2 (G : Type*) [Magma G] (h : Equation24398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24399_implies_Equation2 (G : Type*) [Magma G] (h : Equation24399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24401_implies_Equation2 (G : Type*) [Magma G] (h : Equation24401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq7 eq10
  have eq40 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq25 eq11
  have eq47 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X0)) = X0 := superpose eq40 eq7
  have eq60 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ X2) = X0 := superpose eq40 eq47
  have eq61 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq40 eq60
  have eq62 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq40 eq61
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq62 eq62
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq65 eq63


@[equational_result]
theorem Equation24402_implies_Equation2 (G : Type*) [Magma G] (h : Equation24402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ (((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X3 ◇ X3) ◇ X3))) = X0 := superpose eq9 eq10
  have eq54 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ X3) = X0 := superpose eq7 eq23
  have eq64 (X0 X3 : G) : X0 = X3 := superpose eq7 eq54
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq163 eq64


@[equational_result]
theorem Equation24403_implies_Equation2 (G : Type*) [Magma G] (h : Equation24403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq50 eq16


@[equational_result]
theorem Equation24405_implies_Equation2 (G : Type*) [Magma G] (h : Equation24405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24406_implies_Equation2 (G : Type*) [Magma G] (h : Equation24406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24407_implies_Equation2 (G : Type*) [Magma G] (h : Equation24407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24409_implies_Equation2 (G : Type*) [Magma G] (h : Equation24409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24410_implies_Equation2 (G : Type*) [Magma G] (h : Equation24410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24411_implies_Equation2 (G : Type*) [Magma G] (h : Equation24411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24413_implies_Equation2 (G : Type*) [Magma G] (h : Equation24413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24414_implies_Equation2 (G : Type*) [Magma G] (h : Equation24414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24415_implies_Equation2 (G : Type*) [Magma G] (h : Equation24415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24416_implies_Equation2 (G : Type*) [Magma G] (h : Equation24416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24418_implies_Equation2 (G : Type*) [Magma G] (h : Equation24418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq10
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq15 eq9
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq7 eq24
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq47 eq29


@[equational_result]
theorem Equation24419_implies_Equation2 (G : Type*) [Magma G] (h : Equation24419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq10 eq10
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq7 eq34
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq142 eq39


@[equational_result]
theorem Equation24420_implies_Equation2 (G : Type*) [Magma G] (h : Equation24420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation24422_implies_Equation2 (G : Type*) [Magma G] (h : Equation24422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq13 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq10 eq21
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq48 eq30


@[equational_result]
theorem Equation24423_implies_Equation2 (G : Type*) [Magma G] (h : Equation24423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) = X3 := superpose eq9 eq9
  have eq28 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq17 eq10
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq7 eq28
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq56 eq32


@[equational_result]
theorem Equation24424_implies_Equation2 (G : Type*) [Magma G] (h : Equation24424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X3 X4 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X4)) = X2 := superpose eq7 eq10
  have eq24 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X4)) = X3 := superpose eq13 eq9
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq24
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq55 eq33


@[equational_result]
theorem Equation24427_implies_Equation2 (G : Type*) [Magma G] (h : Equation24427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ X2) = (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = (X3 ◇ X2) := superpose eq9 eq9
  have eq33 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = (((X3 ◇ X3) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq11
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X1) := superpose eq11 eq11
  have eq50 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq9 eq35
  have eq67 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq35 eq9
  have eq106 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq50 eq33
  have eq109 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq67 eq106
  have eq111 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = X2 := superpose eq109 eq14
  have eq126 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq111 eq15
  have eq127 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = X2 := superpose eq126 eq9
  have eq138 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq126 eq127
  have eq140 (X0 X2 : G) : X0 = X2 := superpose eq138 eq138
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq140 eq8
  subsumption eq142 eq140


@[equational_result]
theorem Equation24428_implies_Equation2 (G : Type*) [Magma G] (h : Equation24428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X1 ◇ X1) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq57 (X0 X1 : G) : X0 = X1 := superpose eq7 eq35
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq133 eq57


@[equational_result]
theorem Equation24430_implies_Equation2 (G : Type*) [Magma G] (h : Equation24430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq15 eq9
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation24431_implies_Equation2 (G : Type*) [Magma G] (h : Equation24431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq32 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq9 eq10
  have eq44 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq32 eq10
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq7 eq44
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq107 eq53


@[equational_result]
theorem Equation24432_implies_Equation2 (G : Type*) [Magma G] (h : Equation24432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) = X2 := superpose eq10 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq15
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq119 eq39


@[equational_result]
theorem Equation24433_implies_Equation2 (G : Type*) [Magma G] (h : Equation24433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation24435_implies_Equation2 (G : Type*) [Magma G] (h : Equation24435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq14 eq9
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq10 eq20
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq44 eq26


@[equational_result]
theorem Equation24436_implies_Equation2 (G : Type*) [Magma G] (h : Equation24436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X3) ◇ (X0 ◇ X3)) := superpose eq7 eq11
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) = X0 := superpose eq7 eq13
  have eq39 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq26 eq12
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq39
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq65 eq40


@[equational_result]
theorem Equation24437_implies_Equation2 (G : Type*) [Magma G] (h : Equation24437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq58 eq36


@[equational_result]
theorem Equation24439_implies_Equation2 (G : Type*) [Magma G] (h : Equation24439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation24440_implies_Equation2 (G : Type*) [Magma G] (h : Equation24440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation24441_implies_Equation2 (G : Type*) [Magma G] (h : Equation24441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24443_implies_Equation2 (G : Type*) [Magma G] (h : Equation24443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24444_implies_Equation2 (G : Type*) [Magma G] (h : Equation24444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24445_implies_Equation2 (G : Type*) [Magma G] (h : Equation24445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24447_implies_Equation2 (G : Type*) [Magma G] (h : Equation24447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24448_implies_Equation2 (G : Type*) [Magma G] (h : Equation24448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24449_implies_Equation2 (G : Type*) [Magma G] (h : Equation24449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24450_implies_Equation2 (G : Type*) [Magma G] (h : Equation24450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24453_implies_Equation2 (G : Type*) [Magma G] (h : Equation24453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq9 eq9
  have eq25 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq9 eq11
  have eq34 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq9 eq11
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X0)) ◇ X1) = X0 := superpose eq7 eq11
  have eq49 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq16 eq34
  have eq56 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq11 eq49
  have eq57 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq49 eq49
  have eq63 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1)))) ◇ X1) = (((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq49 eq11
  have eq64 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq57 eq25
  have eq70 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq64 eq7
  have eq71 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq64 eq9
  have eq76 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) = X2 := superpose eq64 eq16
  have eq81 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq64 eq56
  have eq91 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq49 eq70
  have eq97 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq57 eq70
  have eq99 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq97 eq91
  have eq104 (X0 X1 X3 : G) : (((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) ◇ X1) := superpose eq99 eq63
  have eq112 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X2 := superpose eq99 eq71
  have eq116 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq99 eq76
  have eq120 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) := superpose eq99 eq81
  have eq126 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = (((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq36 eq104
  have eq131 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X0 := superpose eq116 eq120
  have eq135 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq131 eq126
  have eq141 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq131 eq135
  have eq147 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq141 eq131
  have eq153 (X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = X2 := superpose eq147 eq112
  have eq162 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq147 eq153
  have eq165 (X0 X2 : G) : X0 = X2 := superpose eq162 eq162
  have eq167 (X0 : G) : sK0 ≠ X0 := superpose eq165 eq8
  subsumption eq167 eq165


@[equational_result]
theorem Equation24454_implies_Equation2 (G : Type*) [Magma G] (h : Equation24454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation24456_implies_Equation2 (G : Type*) [Magma G] (h : Equation24456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24457_implies_Equation2 (G : Type*) [Magma G] (h : Equation24457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24458_implies_Equation2 (G : Type*) [Magma G] (h : Equation24458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24460_implies_Equation2 (G : Type*) [Magma G] (h : Equation24460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24461_implies_Equation2 (G : Type*) [Magma G] (h : Equation24461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24462_implies_Equation2 (G : Type*) [Magma G] (h : Equation24462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24464_implies_Equation2 (G : Type*) [Magma G] (h : Equation24464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24465_implies_Equation2 (G : Type*) [Magma G] (h : Equation24465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24466_implies_Equation2 (G : Type*) [Magma G] (h : Equation24466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24467_implies_Equation2 (G : Type*) [Magma G] (h : Equation24467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24469_implies_Equation2 (G : Type*) [Magma G] (h : Equation24469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X1))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq23 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = X3 := superpose eq15 eq9
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation24470_implies_Equation2 (G : Type*) [Magma G] (h : Equation24470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq9 eq12
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq7 eq32
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq122 eq44


@[equational_result]
theorem Equation24471_implies_Equation2 (G : Type*) [Magma G] (h : Equation24471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq139 eq33


@[equational_result]
theorem Equation24472_implies_Equation2 (G : Type*) [Magma G] (h : Equation24472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation24474_implies_Equation2 (G : Type*) [Magma G] (h : Equation24474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24475_implies_Equation2 (G : Type*) [Magma G] (h : Equation24475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24476_implies_Equation2 (G : Type*) [Magma G] (h : Equation24476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24477_implies_Equation2 (G : Type*) [Magma G] (h : Equation24477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24479_implies_Equation2 (G : Type*) [Magma G] (h : Equation24479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24480_implies_Equation2 (G : Type*) [Magma G] (h : Equation24480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24481_implies_Equation2 (G : Type*) [Magma G] (h : Equation24481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24482_implies_Equation2 (G : Type*) [Magma G] (h : Equation24482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24484_implies_Equation2 (G : Type*) [Magma G] (h : Equation24484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24485_implies_Equation2 (G : Type*) [Magma G] (h : Equation24485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24486_implies_Equation2 (G : Type*) [Magma G] (h : Equation24486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24487_implies_Equation2 (G : Type*) [Magma G] (h : Equation24487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24489_implies_Equation2 (G : Type*) [Magma G] (h : Equation24489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24490_implies_Equation2 (G : Type*) [Magma G] (h : Equation24490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24491_implies_Equation2 (G : Type*) [Magma G] (h : Equation24491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24492_implies_Equation2 (G : Type*) [Magma G] (h : Equation24492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24493_implies_Equation2 (G : Type*) [Magma G] (h : Equation24493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24495_implies_Equation2 (G : Type*) [Magma G] (h : Equation24495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq20 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq29 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq11
  have eq51 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq21 eq21
  have eq68 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq51 eq29
  have eq277 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq68 eq20
  have eq304 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq68 eq277
  have eq307 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq304 eq20
  have eq315 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq304 eq307
  have eq320 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq315 eq21
  have eq376 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq315 eq320
  have eq377 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq315 eq376
  have eq400 (X0 X1 : G) : X0 = X1 := superpose eq315 eq377
  have eq402 (X0 : G) : sK0 ≠ X0 := superpose eq400 eq8
  subsumption eq402 eq400


@[equational_result]
theorem Equation24496_implies_Equation2 (G : Type*) [Magma G] (h : Equation24496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq9 eq9
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq20 eq11
  have eq29 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq26 eq26
  have eq32 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq26 eq26
  have eq34 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X3))) ◇ (X2 ◇ X0)) ◇ X0) := superpose eq9 eq26
  have eq42 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq20
  have eq47 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq20 eq9
  have eq50 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1))) = X0 := superpose eq20 eq9
  have eq52 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq32 eq42
  have eq53 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq20 eq52
  have eq64 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq53 eq18
  have eq71 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))) ◇ (X2 ◇ X0)) ◇ X0) := superpose eq53 eq34
  have eq81 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X0)) ◇ X0) := superpose eq53 eq71
  have eq85 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq53 eq47
  have eq87 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq64 eq50
  have eq88 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq53 eq87
  have eq170 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq88 eq64
  have eq432 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = ((X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq170 eq29
  have eq490 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X3))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq32 eq81
  have eq527 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq88 eq85
  have eq573 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq88 eq527
  have eq576 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq573 eq432
  have eq600 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq53 eq576
  have eq601 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq573 eq600
  have eq602 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq573 eq601
  have eq603 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq602 eq490
  have eq677 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq602 eq603
  have eq678 (X0 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq602 eq677
  have eq679 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq602 eq678
  have eq680 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq602 eq679
  have eq759 (X0 X1 : G) : X0 = X1 := superpose eq680 eq602
  have eq777 (X0 : G) : sK0 ≠ X0 := superpose eq759 eq8
  subsumption eq777 eq759


@[equational_result]
theorem Equation24497_implies_Equation2 (G : Type*) [Magma G] (h : Equation24497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X4 ◇ X4) ◇ X5)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq29 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq12
  have eq46 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq18 eq18
  have eq47 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq18 eq7
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq46 eq29
  have eq59 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq46 eq47
  have eq60 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq59 eq56
  have eq63 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq60 eq12
  have eq70 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X0 := superpose eq60 eq63
  have eq71 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq60 eq70
  have eq75 (X0 X1 : G) : X0 = X1 := superpose eq71 eq60
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq77 eq75


@[equational_result]
theorem Equation24499_implies_Equation2 (G : Type*) [Magma G] (h : Equation24499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ ((X1 ◇ X3) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq9
  have eq18 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq9
  have eq28 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (X2 ◇ ((((X2 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq10 eq10
  have eq29 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) = X0 := superpose eq10 eq9
  have eq77 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq11 eq9
  have eq95 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1)) := superpose eq7 eq18
  have eq107 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq18 eq11
  have eq163 (X0 X1 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose eq107 eq107
  have eq282 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq18 eq28
  have eq284 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X1 ◇ X0))))) := superpose eq16 eq28
  have eq326 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq7 eq282
  have eq345 (X0 X1 : G) : (((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ X0) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1)))) := superpose eq95 eq282
  have eq410 (X0 X1 X2 : G) : ((((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)))) = X0 := superpose eq107 eq77
  have eq429 (X0 X1 X2 X3 : G) : ((((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)) ◇ X3) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq14 eq77
  have eq537 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X0)) = (((X0 ◇ X1) ◇ X2) ◇ ((((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ (((((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq14 eq29
  have eq581 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = (X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X1) ◇ X1)) := superpose eq29 eq18
  have eq817 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))))) := superpose eq28 eq284
  have eq908 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq326 eq817
  have eq909 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq9 eq908
  have eq917 (X0 X1 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1)))) = X0 := superpose eq909 eq345
  have eq921 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq909 eq95
  have eq1067 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose eq909 eq917
  have eq1068 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq909 eq1067
  have eq1103 (X0 X1 X2 : G) : ((((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)))) = X0 := superpose eq921 eq410
  have eq1110 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose eq921 eq163
  have eq1113 (X0 X1 X2 X3 : G) : ((((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0)) ◇ X3) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq921 eq429
  have eq1114 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X0)) = (((X0 ◇ X1) ◇ X2) ◇ (((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ ((((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq921 eq537
  have eq1121 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X1)) := superpose eq921 eq581
  have eq1482 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)))) = X0 := superpose eq921 eq1103
  have eq1483 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)))) = X0 := superpose eq921 eq1482
  have eq1491 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq921 eq1110
  have eq1492 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq921 eq1491
  have eq1498 (X0 X1 X2 X3 : G) : ((((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0)) ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq921 eq1113
  have eq1499 (X0 X1 X2 X3 : G) : ((((X2 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq921 eq1498
  have eq1500 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X0)) = (((X0 ◇ X1) ◇ X2) ◇ (((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ (((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq921 eq1114
  have eq1501 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (((X0 ◇ X1) ◇ X2) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq921 eq1500
  have eq1517 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0))) = (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0))) ◇ X1)) := superpose eq921 eq1121
  have eq1518 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = (X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X1)) := superpose eq921 eq1517
  have eq1519 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq1068 eq1518
  have eq1520 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq921 eq1519
  have eq1521 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq921 eq1520
  have eq1524 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := superpose eq1521 eq1483
  have eq1531 (X0 X1 X2 X3 : G) : ((((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq1521 eq1499
  have eq1541 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (((X0 ◇ X1) ◇ X2) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq1521 eq1501
  have eq1550 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) := superpose eq1521 eq1492
  have eq1553 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq1068 eq1524
  have eq1554 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq1521 eq1553
  have eq1559 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq1521 eq1531
  have eq1560 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq921 eq1559
  have eq1569 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq1521 eq1541
  have eq1570 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq1560 eq1569
  have eq1576 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq1570 eq1554
  have eq1588 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq1068 eq1550
  have eq1589 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq1068 eq1588
  have eq1590 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1589 eq921
  have eq1591 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq1590 eq1576
  have eq1624 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq1590 eq1591
  have eq1653 (X0 X1 : G) : X0 = X1 := superpose eq1590 eq1624
  have eq1663 (X0 : G) : sK0 ≠ X0 := superpose eq1653 eq8
  subsumption eq1663 eq1653


@[equational_result]
theorem Equation24501_implies_Equation2 (G : Type*) [Magma G] (h : Equation24501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X4) ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X1 ◇ X4) ◇ X0)) ◇ (X0 ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ X4) = X0 := superpose eq7 eq12
  have eq18 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) := superpose eq12 eq12
  have eq23 (X0 X1 X4 X5 : G) : ((X1 ◇ X4) ◇ X0) = ((X1 ◇ X4) ◇ (X0 ◇ X5)) := superpose eq18 eq11
  have eq25 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq23 eq12
  have eq26 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq15 eq25
  have eq28 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := superpose eq26 eq7
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq26 eq28
  have eq38 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq26 eq37
  have eq39 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq26 eq38
  have eq49 (X0 X1 : G) : X0 = X1 := superpose eq39 eq26
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq51 eq49


@[equational_result]
theorem Equation24503_implies_Equation2 (G : Type*) [Magma G] (h : Equation24503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = (X0 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq26 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ ((X3 ◇ (X0 ◇ X4)) ◇ ((X4 ◇ ((X0 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0)))) = X3 := superpose eq7 eq9
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((((X3 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0))) := superpose eq9 eq9
  have eq49 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq7 eq34
  have eq50 (X0 X1 X2 : G) : ((((X0 ◇ X2) ◇ X1) ◇ X0) ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) = X0 := superpose eq7 eq49
  have eq51 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq12 eq49
  have eq79 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((((X3 ◇ X1) ◇ X0) ◇ X3) ◇ (X0 ◇ X1))) = (X2 ◇ ((((X2 ◇ X3) ◇ ((((X3 ◇ X1) ◇ X0) ◇ X3) ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ X1))) := superpose eq12 eq10
  have eq80 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ ((X4 ◇ X3) ◇ X2))) ◇ (X2 ◇ X0)) = (X1 ◇ ((((X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ ((X4 ◇ X3) ◇ X2))) ◇ (X2 ◇ X0)) ◇ X1) ◇ X0)) := superpose eq9 eq10
  have eq84 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose eq10 eq49
  have eq99 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq84
  have eq100 (X0 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ X0)) = X0 := superpose eq7 eq51
  have eq106 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X0) := superpose eq7 eq51
  have eq131 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq106 eq99
  have eq142 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((((X3 ◇ X1) ◇ X0) ◇ X3) ◇ (X0 ◇ X1))) = (X2 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1))) := superpose eq106 eq79
  have eq192 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq106 eq131
  have eq193 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq100 eq192
  have eq194 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq193 eq32
  have eq199 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq100 eq194
  have eq201 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ ((X4 ◇ X3) ◇ X2))) ◇ (X2 ◇ X0)) = (X1 ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq199 eq80
  have eq203 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ ((X4 ◇ ((X0 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0)))) = X3 := superpose eq199 eq26
  have eq211 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ ((X4 ◇ X3) ◇ X2))) ◇ (X2 ◇ X0)) := superpose eq199 eq201
  have eq212 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X2 ◇ X0)) := superpose eq199 eq211
  have eq213 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X1 ◇ X3) ◇ (X2 ◇ X0)) := superpose eq199 eq212
  have eq214 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq213 eq203
  have eq215 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq199 eq214
  have eq225 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((((X3 ◇ X1) ◇ X0) ◇ X3) ◇ (X0 ◇ X1))) = (X2 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq213 eq142
  have eq226 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((((X3 ◇ X1) ◇ X0) ◇ X3) ◇ (X0 ◇ X1))) := superpose eq215 eq225
  have eq227 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq199 eq226
  have eq231 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq227 eq199
  have eq237 (X0 X1 : G) : X0 = X1 := superpose eq227 eq231
  have eq247 (X0 : G) : sK0 ≠ X0 := superpose eq237 eq8
  subsumption eq247 eq237


@[equational_result]
theorem Equation24504_implies_Equation2 (G : Type*) [Magma G] (h : Equation24504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = (X0 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X0) = (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X3 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq14 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq9
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)))) := superpose eq9 eq9
  have eq39 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq10 eq21
  have eq60 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X3 ◇ (((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1))) := superpose eq10 eq11
  have eq82 (X0 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq21 eq14
  have eq83 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = (((X1 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0))) := superpose eq14 eq11
  have eq85 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0)) := superpose eq14 eq7
  have eq91 (X0 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq14 eq10
  have eq97 (X0 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))) := superpose eq39 eq82
  have eq101 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X2 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (((X2 ◇ ((X2 ◇ X1) ◇ X1)) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ X3)) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ X3)))) := superpose eq21 eq22
  have eq133 (X0 : G) : (((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq14 eq39
  have eq140 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq11 eq39
  have eq165 (X0 : G) : (((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq7 eq133
  have eq166 (X0 : G) : (((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) := superpose eq39 eq165
  have eq167 (X0 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))) := superpose eq166 eq91
  have eq200 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq140
  have eq203 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq140 eq10
  have eq216 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq140 eq9
  have eq221 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X1) ◇ X1)) ◇ (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X1) ◇ X1))) = X0 := superpose eq140 eq9
  have eq234 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq39 eq200
  have eq235 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) := superpose eq234 eq166
  have eq237 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq235 eq167
  have eq238 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq39 eq237
  have eq243 (X0 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))) := superpose eq238 eq97
  have eq247 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) := superpose eq238 eq235
  have eq249 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))) := superpose eq238 eq243
  have eq254 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq203 eq140
  have eq256 (X0 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq254 eq85
  have eq258 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq254 eq83
  have eq259 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq256
  have eq271 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) := superpose eq259 eq39
  have eq302 (X0 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq259 eq247
  have eq303 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0))) := superpose eq259 eq249
  have eq325 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = (X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X0)) := superpose eq271 eq10
  have eq352 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X3 ◇ ((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1))) := superpose eq271 eq60
  have eq394 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq271 eq302
  have eq395 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq271 eq303
  have eq396 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq325 eq395
  have eq397 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq396
  have eq398 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq397 eq394
  have eq434 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq398 eq258
  have eq435 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq398 eq434
  have eq436 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq398 eq435
  have eq437 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq398 eq436
  have eq482 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq398 eq216
  have eq483 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq398 eq482
  have eq484 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq398 eq483
  have eq485 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq398 eq484
  have eq490 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X1))) = X0 := superpose eq485 eq221
  have eq491 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq437 eq490
  have eq492 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq485 eq491
  have eq493 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq398 eq492
  have eq494 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq398 eq493
  have eq499 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((X3 ◇ ((((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X1))) := superpose eq494 eq352
  have eq501 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X2 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq494 eq101
  have eq534 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq494 eq485
  have eq560 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) := superpose eq494 eq501
  have eq569 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq494 eq534
  have eq575 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X3 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq569 eq499
  have eq613 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq569 eq437
  have eq632 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq398 eq575
  have eq633 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq569 eq632
  have eq634 (X0 X1 X3 : G) : (X0 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := superpose eq569 eq633
  have eq639 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ X2) := superpose eq634 eq560
  have eq645 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq569 eq639
  have eq711 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq613 eq645
  have eq811 (X0 X1 : G) : X0 = X1 := superpose eq613 eq711
  have eq813 (X0 : G) : sK0 ≠ X0 := superpose eq811 eq8
  subsumption eq813 eq811


@[equational_result]
theorem Equation24505_implies_Equation2 (G : Type*) [Magma G] (h : Equation24505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (((X4 ◇ X5) ◇ X0) ◇ X5) = X0 := superpose eq7 eq12
  have eq49 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq15 eq15
  have eq71 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq49 eq7
  have eq85 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq49 eq71
  have eq88 (X0 X2 : G) : X0 = X2 := superpose eq85 eq85
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq90 eq88


@[equational_result]
theorem Equation24507_implies_Equation2 (G : Type*) [Magma G] (h : Equation24507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X4 ◇ X5) ◇ ((X1 ◇ X2) ◇ X0))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X4)) ◇ X0) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq9 eq9
  have eq39 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X3)) := superpose eq7 eq12
  have eq54 (X0 X1 X2 X4 : G) : (X2 ◇ X4) = ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) := superpose eq39 eq12
  have eq67 (X2 X4 : G) : (X2 ◇ X4) = X2 := superpose eq22 eq54
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq67 eq22
  have eq77 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq67 eq68
  have eq78 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq67 eq77
  have eq79 (X0 X3 : G) : X0 = X3 := superpose eq78 eq78
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq84 eq79


@[equational_result]
theorem Equation24508_implies_Equation2 (G : Type*) [Magma G] (h : Equation24508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X4 ◇ X5) ◇ ((X0 ◇ X3) ◇ X2))) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X2) = (X0 ◇ ((((X0 ◇ X3) ◇ X2) ◇ X4) ◇ X0)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X4) ◇ X0)) = X3 := superpose eq7 eq9
  have eq27 (X0 X1 X2 X4 X5 : G) : (X0 ◇ X4) = (((X1 ◇ X2) ◇ X0) ◇ (((X0 ◇ X4) ◇ X5) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq10
  have eq29 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = (X0 ◇ (((((X0 ◇ X1) ◇ X2) ◇ X4) ◇ X5) ◇ X0)) := superpose eq10 eq10
  have eq35 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0)) := superpose eq10 eq10
  have eq46 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ X4) := superpose eq35 eq29
  have eq47 (X0 X1 X2 X4 X5 : G) : (X0 ◇ X4) = (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X4) ◇ X5)) := superpose eq46 eq27
  have eq54 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq19 eq47
  have eq55 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := superpose eq54 eq7
  have eq72 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq54 eq55
  have eq73 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq54 eq72
  have eq74 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq54 eq73
  have eq96 (X0 X1 : G) : X0 = X1 := superpose eq74 eq54
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq114 eq96


@[equational_result]
theorem Equation24509_implies_Equation2 (G : Type*) [Magma G] (h : Equation24509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X4 ◇ X5) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = (X0 ◇ ((((X0 ◇ X3) ◇ X3) ◇ X4) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ X0) = (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X5) ◇ X5))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3))) = X0 := superpose eq10 eq9
  have eq30 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ ((X2 ◇ X3) ◇ X0)) = (X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X4) ◇ X4)))) := superpose eq7 eq22
  have eq32 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = (X2 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ X3)))) := superpose eq10 eq22
  have eq46 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ ((X2 ◇ X3) ◇ X0)) = (X1 ◇ ((((X2 ◇ X3) ◇ X0) ◇ X0) ◇ X0)) := superpose eq22 eq30
  have eq48 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (X2 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq22 eq32
  have eq49 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (X2 ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1))) := superpose eq46 eq48
  have eq50 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq10 eq49
  have eq81 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ ((((X2 ◇ X3) ◇ X4) ◇ X4) ◇ (((((X2 ◇ X3) ◇ X4) ◇ X4) ◇ X5) ◇ X5))) := superpose eq22 eq11
  have eq87 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ ((X0 ◇ X1) ◇ X2))) = (((X7 ◇ X8) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X5 ◇ X6) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X9) ◇ X9))))) := superpose eq11 eq11
  have eq89 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = ((((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) ◇ X4) := superpose eq22 eq11
  have eq99 (X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) := superpose eq25 eq81
  have eq114 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ ((X0 ◇ X1) ◇ X2))) = (((X7 ◇ X8) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X5 ◇ X6) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2))) := superpose eq22 eq87
  have eq115 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ ((X0 ◇ X1) ◇ X2))) = (((X7 ◇ X8) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ ((X0 ◇ X1) ◇ X2)))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq114
  have eq124 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X3)) = (((X1 ◇ X2) ◇ X0) ◇ ((((X0 ◇ X3) ◇ X3) ◇ X4) ◇ X4)) := superpose eq7 eq50
  have eq127 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq50 eq50
  have eq196 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) = X1 := superpose eq7 eq127
  have eq197 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X3)) = X0 := superpose eq196 eq124
  have eq201 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X0) := superpose eq197 eq11
  have eq203 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq197 eq15
  have eq206 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq197 eq22
  have eq207 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = (((X2 ◇ X3) ◇ X4) ◇ X4) := superpose eq201 eq89
  have eq212 (X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X4)) := superpose eq207 eq99
  have eq222 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X4 ◇ X5)) = X4 := superpose eq206 eq9
  have eq223 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq206 eq50
  have eq230 (X0 X1 X2 : G) : (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := superpose eq206 eq223
  have eq231 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ (X0 ◇ X1))) = (((X7 ◇ X8) ◇ ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq230 eq115
  have eq237 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X2 ◇ X0) := superpose eq230 eq203
  have eq238 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ (X0 ◇ X1))) = (((X7 ◇ X8) ◇ (X3 ◇ X4)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq230 eq231
  have eq239 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ (X0 ◇ X1))) = (((X7 ◇ X8) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq230 eq238
  have eq240 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (((X7 ◇ X8) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ X0)) := superpose eq230 eq239
  have eq252 (X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ (X3 ◇ X4)) := superpose eq237 eq212
  have eq254 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ X0)) = (((X7 ◇ X8) ◇ X3) ◇ (X1 ◇ X2)) := superpose eq237 eq240
  have eq258 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq222 eq252
  have eq262 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq258 eq222
  have eq265 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq258 eq262
  have eq269 (X0 X2 X3 X4 X5 X6 X7 X8 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ X0)) = (((X7 ◇ X8) ◇ X3) ◇ X2) := superpose eq258 eq254
  have eq270 (X0 X2 X3 X4 X5 X6 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ X0)) = (X3 ◇ X2) := superpose eq258 eq269
  have eq271 (X0 X3 X4 X5 X6 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X6) ◇ X0)) = X3 := superpose eq265 eq270
  have eq272 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = X3 := superpose eq258 eq271
  have eq273 (X0 X3 X4 : G) : (X4 ◇ X0) = X3 := superpose eq258 eq272
  have eq274 (X0 X3 : G) : X0 = X3 := superpose eq273 eq273
  have eq279 (X0 : G) : sK0 ≠ X0 := superpose eq274 eq8
  subsumption eq279 eq274


@[equational_result]
theorem Equation24510_implies_Equation2 (G : Type*) [Magma G] (h : Equation24510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ ((X5 ◇ X6) ◇ X7)) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9
  have eq27 (X0 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X4)) = X0 := superpose eq18 eq7
  have eq29 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq18 eq27
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation24512_implies_Equation2 (G : Type*) [Magma G] (h : Equation24512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq9
  have eq18 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq9
  have eq43 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq16 eq16
  have eq100 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) := superpose eq7 eq18
  have eq113 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq18 eq16
  have eq140 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq113 eq100
  have eq146 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq140 eq43
  have eq147 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq140 eq14
  have eq156 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1))) = ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq147 eq147
  have eq166 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ (X1 ◇ X0)) = (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X3))) := superpose eq147 eq147
  have eq169 (X0 X1 X2 X3 : G) : ((X1 ◇ ((((X2 ◇ X3) ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X1))) ◇ X1) = (((((X2 ◇ X3) ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) ◇ (((((X2 ◇ X3) ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0)) := superpose eq9 eq147
  have eq175 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq9 eq147
  have eq176 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq16 eq147
  have eq227 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = (((X1 ◇ X0) ◇ X3) ◇ (X1 ◇ X0)) := superpose eq147 eq166
  have eq228 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq227 eq10
  have eq288 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) := superpose eq227 eq169
  have eq294 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq227 eq175
  have eq295 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq113 eq176
  have eq296 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq295 eq294
  have eq299 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose eq296 eq288
  have eq372 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose eq228 eq228
  have eq390 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := superpose eq299 eq372
  have eq398 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq390 eq228
  have eq399 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq140 eq398
  have eq400 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq399 eq146
  have eq464 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1))) := superpose eq400 eq156
  have eq476 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq400 eq464
  have eq477 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq476 eq400
  have eq478 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq477 eq399
  have eq529 (X0 X2 : G) : X0 = X2 := superpose eq478 eq478
  have eq531 (X0 : G) : sK0 ≠ X0 := superpose eq529 eq8
  subsumption eq531 eq529


@[equational_result]
theorem Equation24513_implies_Equation2 (G : Type*) [Magma G] (h : Equation24513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ ((X1 ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq12
  have eq21 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq7
  have eq23 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq17
  have eq54 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq23
  have eq56 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq23 eq7
  have eq57 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq23 eq9
  have eq72 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) ◇ X0) = (X3 ◇ ((X0 ◇ (((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) ◇ X0)) ◇ X3)) := superpose eq12 eq10
  have eq74 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose eq23 eq10
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (X0 ◇ ((((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq12 eq10
  have eq79 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq23 eq10
  have eq99 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq23 eq79
  have eq100 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq99 eq74
  have eq101 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X1 ◇ X1) := superpose eq54 eq100
  have eq102 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq23 eq101
  have eq104 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X2 := superpose eq102 eq57
  have eq105 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq102 eq56
  have eq107 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) ◇ X0) = (X3 ◇ (((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) ◇ X3)) := superpose eq105 eq72
  have eq109 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) = (((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) ◇ X0) := superpose eq105 eq107
  have eq113 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) ◇ (X0 ◇ X3)) = X0 := superpose eq109 eq21
  have eq114 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X0)) := superpose eq113 eq77
  have eq116 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq105 eq114
  have eq117 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq116 eq104
  have eq159 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq116 eq117
  have eq160 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq116 eq159
  have eq161 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq116 eq160
  have eq162 (X0 X1 : G) : X0 = X1 := superpose eq23 eq161
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq162 eq8
  subsumption eq170 eq162


@[equational_result]
theorem Equation24514_implies_Equation2 (G : Type*) [Magma G] (h : Equation24514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X4) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X3) = (X0 ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X4)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq29 (X0 X1 X2 X3 X5 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ ((X0 ◇ X3) ◇ X5)) = X3 := superpose eq7 eq9
  have eq33 (X0 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X4)) = X0 := superpose eq12 eq9
  have eq46 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq18 eq33
  have eq61 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq18 eq7
  have eq65 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq46 eq61
  have eq70 (X0 X1 X2 X3 X4 X7 : G) : ((X1 ◇ X3) ◇ X4) = (X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) ◇ X7)) := superpose eq10 eq10
  have eq79 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq18 eq10
  have eq104 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq65 eq79
  have eq105 (X0 X1 X2 X3 X4 X7 : G) : ((X1 ◇ X3) ◇ X4) = (X3 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X7)) := superpose eq104 eq70
  have eq115 (X1 X3 X4 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ X4) := superpose eq104 eq105
  have eq116 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ X5)) = X4 := superpose eq115 eq9
  have eq121 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X3) ◇ X5)) = X3 := superpose eq115 eq29
  have eq136 (X0 X1 X2 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ X2) ◇ X0)) = X4 := superpose eq115 eq116
  have eq137 (X0 X1 X2 X4 : G) : ((X0 ◇ X4) ◇ (X1 ◇ X2)) = X4 := superpose eq115 eq136
  have eq138 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq137 eq65
  have eq147 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ X5) = X3 := superpose eq138 eq121
  have eq148 (X2 X3 X5 : G) : (X2 ◇ X5) = X3 := superpose eq138 eq147
  have eq149 (X0 X1 : G) : X0 = X1 := superpose eq18 eq148
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq149 eq8
  subsumption eq157 eq149


@[equational_result]
theorem Equation24516_implies_Equation2 (G : Type*) [Magma G] (h : Equation24516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq7 eq10
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq102 eq44


@[equational_result]
theorem Equation24518_implies_Equation2 (G : Type*) [Magma G] (h : Equation24518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X5)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq12 eq12
  have eq17 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X0) = X5 := superpose eq7 eq12
  have eq22 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ X2) ◇ X5)) = X4 := superpose eq16 eq9
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq22
  have eq45 (X0 X4 X5 : G) : (X4 ◇ X0) = X5 := superpose eq30 eq17
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq45 eq45
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq61 eq49


@[equational_result]
theorem Equation24520_implies_Equation2 (G : Type*) [Magma G] (h : Equation24520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq9
  have eq24 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (X4 ◇ ((X0 ◇ X4) ◇ X0)) := superpose eq10 eq9
  have eq58 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq24
  have eq75 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq24 eq7
  have eq107 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq9 eq75
  have eq108 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq107
  have eq109 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq108 eq20
  have eq115 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq108 eq58
  have eq145 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq115 eq109
  have eq153 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq115 eq145
  have eq154 (X0 X1 : G) : X0 = X1 := superpose eq153 eq115
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq154 eq8
  subsumption eq156 eq154


@[equational_result]
theorem Equation24521_implies_Equation2 (G : Type*) [Magma G] (h : Equation24521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ X4))) := superpose eq7 eq10
  have eq34 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq9
  have eq47 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) = X3 := superpose eq9 eq10
  have eq51 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq7 eq34
  have eq63 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ X4))) = X2 := superpose eq51 eq12
  have eq77 (X0 X1 X2 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X4)) = X2 := superpose eq51 eq63
  have eq90 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X3 := superpose eq51 eq47
  have eq91 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq90 eq77
  have eq107 (X0 X2 : G) : X0 = X2 := superpose eq91 eq91
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq112 eq107


@[equational_result]
theorem Equation24522_implies_Equation2 (G : Type*) [Magma G] (h : Equation24522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X0 ◇ X5)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq24 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq11 eq11
  have eq33 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq24 eq11
  have eq42 (X0 X2 : G) : X0 = X2 := superpose eq10 eq33
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq51 eq42


@[equational_result]
theorem Equation24524_implies_Equation2 (G : Type*) [Magma G] (h : Equation24524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X3) ◇ X1) = (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq7 eq10
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq152 eq73


@[equational_result]
theorem Equation24525_implies_Equation2 (G : Type*) [Magma G] (h : Equation24525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X3) ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) ◇ X5) ◇ X4)) = X0 := superpose eq7 eq10
  have eq39 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq12 eq16
  have eq70 (X0 X4 : G) : X0 = X4 := superpose eq7 eq39
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq162 eq70


@[equational_result]
theorem Equation24526_implies_Equation2 (G : Type*) [Magma G] (h : Equation24526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X5) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X3) ◇ X3) = (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ X4)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X6) ◇ X6)) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 X5 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ ((X0 ◇ X5) ◇ X5)) = X3 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X4 := superpose eq7 eq9
  have eq64 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X2 ◇ X3) ◇ X4) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X5) ◇ X6) ◇ X6))) = X4 := superpose eq10 eq7
  have eq74 (X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X1) = X4 := superpose eq21 eq64
  have eq75 (X0 X2 X3 X5 : G) : (X2 ◇ ((X0 ◇ X5) ◇ X5)) = X3 := superpose eq74 eq17
  have eq92 (X1 X2 X6 : G) : ((X1 ◇ X2) ◇ X6) = X2 := superpose eq74 eq15
  have eq107 (X2 X3 X5 : G) : (X2 ◇ X5) = X3 := superpose eq92 eq75
  have eq109 (X0 X3 : G) : X0 = X3 := superpose eq107 eq107
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq109 eq8
  subsumption eq120 eq109


@[equational_result]
theorem Equation24527_implies_Equation2 (G : Type*) [Magma G] (h : Equation24527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X6) ◇ X7)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq12 eq9
  have eq15 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq14 eq12
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq30 eq18


@[equational_result]
theorem Equation24530_implies_Equation2 (G : Type*) [Magma G] (h : Equation24530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ ((X3 ◇ X0) ◇ X3)) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq12
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq12
  have eq17 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq12 eq12
  have eq18 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq12 eq7
  have eq20 (X0 X3 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq12 eq7
  have eq21 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq16 eq18
  have eq93 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) := superpose eq15 eq10
  have eq105 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq12 eq11
  have eq150 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq7 eq105
  have eq151 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq150 eq93
  have eq152 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq15 eq151
  have eq153 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq21 eq152
  have eq181 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq153 eq153
  have eq203 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq153 eq181
  have eq204 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq15 eq203
  have eq259 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq204
  have eq293 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X0)) := superpose eq259 eq10
  have eq355 (X0 X1 X2 X3 : G) : (X1 ◇ ((X3 ◇ X0) ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq11 eq20
  have eq356 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) = X0 := superpose eq17 eq20
  have eq369 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq20 eq11
  have eq375 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq20 eq11
  have eq390 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq293 eq356
  have eq391 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq390 eq259
  have eq427 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq391 eq150
  have eq437 (X0 X1 X2 X3 : G) : (X1 ◇ ((X3 ◇ X0) ◇ X1)) = (X1 ◇ (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X1)) ◇ X1))) := superpose eq391 eq355
  have eq458 (X0 X1 X3 : G) : (X1 ◇ ((X3 ◇ X0) ◇ X1)) = X1 := superpose eq427 eq437
  have eq489 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq458 eq369
  have eq490 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq458 eq489
  have eq491 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq391 eq490
  have eq514 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq491 eq375
  have eq515 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq491 eq514
  have eq516 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq491 eq515
  have eq517 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq491 eq516
  have eq518 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq491 eq517
  have eq520 (X0 X2 : G) : X0 = X2 := superpose eq518 eq518
  have eq528 (X0 : G) : sK0 ≠ X0 := superpose eq520 eq8
  subsumption eq528 eq520


@[equational_result]
theorem Equation24531_implies_Equation2 (G : Type*) [Magma G] (h : Equation24531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X2 ◇ X0) ◇ X3) ◇ X4) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : ((X0 ◇ X4) ◇ X4) = X4 := superpose eq7 eq12
  have eq26 (X0 X1 X2 X3 X5 X6 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (((X0 ◇ X5) ◇ X3) ◇ X6)) = X3 := superpose eq7 eq9
  have eq32 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X4)) := superpose eq7 eq9
  have eq45 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq7 eq15
  have eq53 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq15 eq9
  have eq61 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) := superpose eq45 eq10
  have eq65 (X0 X4 X5 : G) : (X0 ◇ X4) = (X0 ◇ ((X0 ◇ X4) ◇ X5)) := superpose eq12 eq61
  have eq94 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X0 ◇ X4)) := superpose eq65 eq32
  have eq95 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq53 eq94
  have eq98 (X0 X2 X3 X5 X6 : G) : (X2 ◇ (((X0 ◇ X5) ◇ X3) ◇ X6)) = X3 := superpose eq95 eq26
  have eq106 (X0 X2 X3 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq95 eq7
  have eq118 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq95 eq98
  have eq132 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq118 eq106
  have eq133 (X0 X3 : G) : X0 = X3 := superpose eq132 eq132
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq133 eq8
  subsumption eq135 eq133


@[equational_result]
theorem Equation24535_implies_Equation2 (G : Type*) [Magma G] (h : Equation24535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X2 ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X5)) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (X3 ◇ X5)) = X4 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq13
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X1) ◇ X3)) = X0 := superpose eq16 eq7
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq16 eq23
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq13 eq26
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq36 eq27


@[equational_result]
theorem Equation24538_implies_Equation2 (G : Type*) [Magma G] (h : Equation24538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ ((((X2 ◇ X2) ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) ◇ ((X2 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X2 ◇ X2) ◇ X2) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X2 ◇ X2) ◇ X2)) = X3 := superpose eq7 eq9
  have eq34 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq13 eq10
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq34 eq34
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq114 eq52


@[equational_result]
theorem Equation24539_implies_Equation2 (G : Type*) [Magma G] (h : Equation24539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X2 ◇ X2) ◇ X3) ◇ ((X2 ◇ X2) ◇ X3)) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ X3) = (X0 ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (X3 ◇ X5)) = X4 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq13
  have eq22 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = (X0 ◇ X0) := superpose eq16 eq10
  have eq27 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq13 eq22
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq13 eq27
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq73 eq40


@[equational_result]
theorem Equation24541_implies_Equation2 (G : Type*) [Magma G] (h : Equation24541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X2 ◇ X3) ◇ X1) ◇ X5) ◇ ((X1 ◇ X2) ◇ X0))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X1) = (X0 ◇ ((X0 ◇ X4) ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq50 (X0 X1 X2 X3 X5 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X5) ◇ ((X2 ◇ X0) ◇ X3)) = X5 := superpose eq10 eq11
  have eq69 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq50 eq9
  have eq73 (X0 X2 X3 X5 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X3)) = X5 := superpose eq69 eq50
  have eq104 (X0 X2 X5 : G) : (X2 ◇ X0) = X5 := superpose eq69 eq73
  have eq105 (X0 X3 : G) : X0 = X3 := superpose eq104 eq104
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq113 eq105


@[equational_result]
theorem Equation24542_implies_Equation2 (G : Type*) [Magma G] (h : Equation24542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X2 ◇ X3) ◇ X2) ◇ X5) ◇ ((X2 ◇ X3) ◇ X2))) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq13 eq16
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq45 eq30


@[equational_result]
theorem Equation24543_implies_Equation2 (G : Type*) [Magma G] (h : Equation24543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X2 ◇ X3) ◇ X3) ◇ X5) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X3) = (X0 ◇ ((X0 ◇ X4) ◇ X4)) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X4) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X3 ◇ X5) ◇ X5))) = X4 := superpose eq10 eq7
  have eq47 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) = X3 := superpose eq7 eq9
  have eq61 (X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X1) = X4 := superpose eq47 eq29
  have eq66 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq61 eq9
  have eq88 (X1 X3 X4 : G) : (X3 ◇ X1) = X4 := superpose eq66 eq61
  have eq91 (X0 X3 : G) : X0 = X3 := superpose eq88 eq88
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq91 eq8
  subsumption eq99 eq91


@[equational_result]
theorem Equation24544_implies_Equation2 (G : Type*) [Magma G] (h : Equation24544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ ((((X2 ◇ X3) ◇ X4) ◇ X6) ◇ X7)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq12
  have eq15 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq23 (X0 X4 X5 X7 : G) : ((X0 ◇ X5) ◇ (X4 ◇ X7)) = X5 := superpose eq13 eq9
  have eq24 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq15 eq13
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq23 eq24
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq49 eq31


@[equational_result]
theorem Equation24546_implies_Equation2 (G : Type*) [Magma G] (h : Equation24546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ X4) ◇ ((X1 ◇ X2) ◇ X0))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X1) = (X0 ◇ ((X4 ◇ ((X3 ◇ X0) ◇ X1)) ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq19 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq54 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq19 eq9
  have eq60 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq19 eq54
  have eq70 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X6 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X3 ◇ X5)) ◇ X7))) := superpose eq10 eq10
  have eq81 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq12 eq10
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq19 eq10
  have eq95 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq19 eq81
  have eq96 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X2 ◇ X0) := superpose eq60 eq82
  have eq103 (X0 X1 X2 X3 X5 X6 X7 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X6 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ ((X3 ◇ X5) ◇ X7))) := superpose eq96 eq70
  have eq119 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = X2 := superpose eq96 eq60
  have eq134 (X0 X1 X2 X3 X5 X7 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ ((X3 ◇ X5) ◇ X7))) := superpose eq96 eq103
  have eq135 (X0 X1 X2 X3 X5 X7 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X3 ◇ ((X3 ◇ X5) ◇ X7))) := superpose eq96 eq134
  have eq136 (X0 X1 X2 X3 X5 X7 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X3 ◇ (X5 ◇ X7))) := superpose eq96 eq135
  have eq154 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq119 eq95
  have eq156 (X2 X3 X5 X7 : G) : (X2 ◇ (X3 ◇ (X5 ◇ X7))) = X3 := superpose eq154 eq136
  have eq167 (X2 X3 X5 X7 : G) : (X2 ◇ (X5 ◇ X7)) = X3 := superpose eq154 eq156
  have eq168 (X2 X3 X7 : G) : (X2 ◇ X7) = X3 := superpose eq154 eq167
  have eq169 (X0 X1 : G) : X0 = X1 := superpose eq19 eq168
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq169 eq8
  subsumption eq177 eq169


@[equational_result]
theorem Equation24547_implies_Equation2 (G : Type*) [Magma G] (h : Equation24547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X2) = (X0 ◇ ((X4 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq17 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq12
  have eq18 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X1) = X1 := superpose eq12 eq12
  have eq20 (X0 X4 : G) : (X0 ◇ ((X4 ◇ X0) ◇ X0)) = X0 := superpose eq12 eq7
  have eq45 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq7 eq17
  have eq58 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq20 eq45
  have eq59 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq58 eq20
  have eq72 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq91 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq59 eq72
  have eq92 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq59 eq91
  have eq93 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq92 eq18
  have eq116 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq93 eq92
  have eq119 (X0 X1 : G) : X0 = X1 := superpose eq93 eq116
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq132 eq119


@[equational_result]
theorem Equation24548_implies_Equation2 (G : Type*) [Magma G] (h : Equation24548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ X3) = (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ (X0 ◇ ((X4 ◇ X5) ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X0 ◇ ((X3 ◇ X0) ◇ X3)) := superpose eq7 eq12
  have eq17 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq12 eq7
  have eq21 (X0 X3 : G) : ((X3 ◇ X0) ◇ X3) = X0 := superpose eq17 eq15
  have eq23 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X4 ◇ X5) ◇ X0))) = X0 := superpose eq21 eq11
  have eq33 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X0 ◇ X3))) = X3 := superpose eq12 eq23
  have eq58 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq21 eq21
  have eq60 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq21 eq12
  have eq63 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq58 eq33
  have eq68 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq60 eq63
  have eq74 (X0 X1 : G) : X0 = X1 := superpose eq68 eq60
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq87 eq74


@[equational_result]
theorem Equation24549_implies_Equation2 (G : Type*) [Magma G] (h : Equation24549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X0 ◇ ((X3 ◇ X0) ◇ X4)) := superpose eq7 eq12
  have eq18 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X4)) = X0 := superpose eq12 eq7
  have eq21 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = X0 := superpose eq18 eq15
  have eq22 (X0 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X4)) = X0 := superpose eq21 eq7
  have eq28 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq21 eq22
  have eq30 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq28 eq21
  have eq37 (X0 X1 : G) : X0 = X1 := superpose eq28 eq30
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq39 eq37


@[equational_result]
theorem Equation24551_implies_Equation2 (G : Type*) [Magma G] (h : Equation24551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq7 eq10
  have eq98 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq174 eq98


@[equational_result]
theorem Equation24552_implies_Equation2 (G : Type*) [Magma G] (h : Equation24552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X2) = (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq30 (X0 X1 X5 X6 : G) : (X5 ◇ ((X6 ◇ (X0 ◇ X1)) ◇ X5)) = X0 := superpose eq12 eq10
  have eq65 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X2) = X1 := superpose eq30 eq10
  have eq68 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X1) ◇ X2)) = X0 := superpose eq65 eq7
  have eq82 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq65 eq68
  have eq83 (X0 X3 : G) : X0 = X3 := superpose eq82 eq82
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq85 eq83


@[equational_result]
theorem Equation24553_implies_Equation2 (G : Type*) [Magma G] (h : Equation24553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X4)) := superpose eq7 eq7
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq7 eq10
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq168 eq69


@[equational_result]
theorem Equation24554_implies_Equation2 (G : Type*) [Magma G] (h : Equation24554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X4) = (X0 ◇ (X1 ◇ X2)) := superpose eq7 eq12
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq12 eq12
  have eq22 (X1 X3 X4 : G) : ((X3 ◇ X1) ◇ X4) = X1 := superpose eq16 eq15
  have eq25 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X1) ◇ X4)) = X0 := superpose eq22 eq7
  have eq29 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq22 eq25
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation24556_implies_Equation2 (G : Type*) [Magma G] (h : Equation24556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 X6 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X6) ◇ X5) = X6 := superpose eq7 eq12
  have eq18 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq12 eq12
  have eq26 (X5 X6 : G) : (X5 ◇ X5) = X6 := superpose eq18 eq13
  have eq36 (X0 X2 : G) : X0 = X2 := superpose eq26 eq26
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq38 eq36


@[equational_result]
theorem Equation24557_implies_Equation2 (G : Type*) [Magma G] (h : Equation24557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X2) = (X0 ◇ ((X4 ◇ X0) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) = X3 := superpose eq7 eq7
  have eq24 (X0 X1 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X4 ◇ X3) ◇ X3)) = X3 := superpose eq10 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X4 := superpose eq10 eq7
  have eq28 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X4) ◇ ((X5 ◇ X3) ◇ X3)) = X4 := superpose eq10 eq7
  have eq38 (X0 X1 X3 X4 : G) : ((X3 ◇ X4) ◇ X4) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X3 ◇ X4) ◇ X4)) := superpose eq10 eq12
  have eq57 (X3 X4 : G) : ((X3 ◇ X4) ◇ X4) = X4 := superpose eq24 eq38
  have eq68 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ ((X4 ◇ X3) ◇ X3)) = X3 := superpose eq57 eq24
  have eq69 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X0)) = X4 := superpose eq57 eq25
  have eq71 (X0 X3 X4 X5 : G) : (((X0 ◇ X0) ◇ X4) ◇ ((X5 ◇ X3) ◇ X3)) = X4 := superpose eq57 eq28
  have eq76 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq57 eq68
  have eq77 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ X3) = X4 := superpose eq57 eq71
  have eq78 (X3 X4 : G) : (X4 ◇ X3) = X4 := superpose eq76 eq77
  have eq79 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X0)) = X4 := superpose eq78 eq69
  have eq88 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X0) = X4 := superpose eq78 eq79
  have eq89 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq78 eq88
  have eq90 (X0 X3 : G) : X0 = X3 := superpose eq89 eq89
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq95 eq90


@[equational_result]
theorem Equation24558_implies_Equation2 (G : Type*) [Magma G] (h : Equation24558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq25 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq14 eq12
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq25 eq25
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation24559_implies_Equation2 (G : Type*) [Magma G] (h : Equation24559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq21 (X0 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X2) ◇ X4)) = X0 := superpose eq14 eq7
  have eq27 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq14 eq21
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq27 eq27
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation24561_implies_Equation2 (G : Type*) [Magma G] (h : Equation24561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq11
  have eq18 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq11 eq11
  have eq23 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq18 eq17
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq156 eq47


@[equational_result]
theorem Equation24562_implies_Equation2 (G : Type*) [Magma G] (h : Equation24562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ X5) ◇ ((X3 ◇ X3) ◇ X2))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = (X0 ◇ (X4 ◇ X0)) := superpose eq11 eq11
  have eq126 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq16 eq9
  have eq160 (X0 X3 : G) : X0 = X3 := superpose eq126 eq126
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq160 eq8
  subsumption eq182 eq160


@[equational_result]
theorem Equation24563_implies_Equation2 (G : Type*) [Magma G] (h : Equation24563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X3 ◇ X3) ◇ X3) = (X0 ◇ ((X4 ◇ X4) ◇ X4)) := superpose eq7 eq7
  have eq37 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq7 eq10
  have eq64 (X0 X2 : G) : X0 = X2 := superpose eq37 eq37
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq138 eq64


@[equational_result]
theorem Equation24564_implies_Equation2 (G : Type*) [Magma G] (h : Equation24564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ ((X6 ◇ X6) ◇ X7)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X5)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9
  have eq26 (X0 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X5)) = X3 := superpose eq18 eq11
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq26 eq26
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation24566_implies_Equation2 (G : Type*) [Magma G] (h : Equation24566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X0) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq11 eq11
  have eq23 (X0 X4 X5 : G) : (X4 ◇ X0) = X5 := superpose eq18 eq12
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation24567_implies_Equation2 (G : Type*) [Magma G] (h : Equation24567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : ((X3 ◇ X4) ◇ X2) = (X0 ◇ ((X5 ◇ X6) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) ◇ X0) = X5 := superpose eq7 eq7
  have eq27 (X0 X5 X6 X7 : G) : (X5 ◇ ((X6 ◇ X7) ◇ X5)) = X0 := superpose eq7 eq10
  have eq113 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq152 (X0 X5 X7 : G) : (X5 ◇ X7) = X0 := superpose eq113 eq27
  have eq161 (X0 X3 : G) : X0 = X3 := superpose eq152 eq152
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq161 eq8
  subsumption eq183 eq161


@[equational_result]
theorem Equation24568_implies_Equation2 (G : Type*) [Magma G] (h : Equation24568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation24569_implies_Equation2 (G : Type*) [Magma G] (h : Equation24569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 X6 : G) : ((X3 ◇ X4) ◇ X4) = (X0 ◇ ((X5 ◇ X6) ◇ X6)) := superpose eq7 eq7
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq7 eq10
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq154 eq69


@[equational_result]
theorem Equation24570_implies_Equation2 (G : Type*) [Magma G] (h : Equation24570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq12
  have eq21 (X0 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X4) ◇ X5)) = X0 := superpose eq13 eq7
  have eq26 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq13 eq21
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation24572_implies_Equation2 (G : Type*) [Magma G] (h : Equation24572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq10
  have eq14 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) = X2 := superpose eq10 eq7
  have eq16 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ X2) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ X0) = X1 := superpose eq10 eq7
  have eq17 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose eq14 eq16
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq11
  have eq19 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq11
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq10 eq11
  have eq28 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1)) = (((((X0 ◇ X0) ◇ X1) ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq7 eq11
  have eq31 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) = (((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) := superpose eq11 eq11
  have eq34 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq11 eq7
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X2 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) := superpose eq11 eq10
  have eq42 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X2 ◇ X3) ◇ X2) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq11 eq7
  have eq47 (X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1)) = X1 := superpose eq17 eq28
  have eq50 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X2 ◇ X2)) = (((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) := superpose eq22 eq31
  have eq51 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X2) = (((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0))) := superpose eq11 eq50
  have eq53 (X2 : G) : ((X2 ◇ X2) ◇ X2) = X2 := superpose eq34 eq51
  have eq54 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq53 eq11
  have eq55 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq53 eq13
  have eq56 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq53 eq18
  have eq65 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq53 eq19
  have eq66 (X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) = X1 := superpose eq54 eq47
  have eq67 (X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X2) = X2 := superpose eq54 eq34
  have eq70 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq54 eq56
  have eq73 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq70 eq15
  have eq76 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq70 eq55
  have eq78 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq70 eq76
  have eq86 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X0 := superpose eq66 eq65
  have eq99 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X2 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq73 eq41
  have eq100 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq73 eq99
  have eq101 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq78 eq100
  have eq104 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq101 eq67
  have eq106 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := superpose eq101 eq86
  have eq108 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := superpose eq101 eq106
  have eq109 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq101 eq42
  have eq110 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq78 eq109
  have eq111 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq73 eq110
  have eq112 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq111 eq101
  have eq114 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := superpose eq112 eq108
  have eq115 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq112 eq104
  have eq117 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq112 eq114
  have eq118 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq115 eq111
  have eq119 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X0 := superpose eq118 eq117
  have eq125 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X0 := superpose eq118 eq119
  have eq126 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq118 eq125
  have eq130 (X0 X1 : G) : X0 = X1 := superpose eq118 eq126
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq130 eq8
  subsumption eq143 eq130


@[equational_result]
theorem Equation24574_implies_Equation2 (G : Type*) [Magma G] (h : Equation24574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X2) ◇ X3)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq132 eq39


@[equational_result]
theorem Equation24576_implies_Equation2 (G : Type*) [Magma G] (h : Equation24576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq17 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ ((X4 ◇ X0) ◇ X0)) = X4 := superpose eq9 eq9
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = (((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq10 eq10
  have eq68 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq7 eq35
  have eq76 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq17 eq35
  have eq95 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq35 eq17
  have eq144 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X2) ◇ X0) := superpose eq76 eq33
  have eq149 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X0 := superpose eq95 eq144
  have eq152 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq149 eq68
  have eq184 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq149 eq152
  have eq185 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq184 eq76
  have eq194 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq184 eq185
  have eq195 (X0 X3 : G) : X0 = X3 := superpose eq194 eq194
  have eq200 (X0 : G) : sK0 ≠ X0 := superpose eq195 eq8
  subsumption eq200 eq195


@[equational_result]
theorem Equation24577_implies_Equation2 (G : Type*) [Magma G] (h : Equation24577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = (((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq11 eq7
  have eq311 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := superpose eq7 eq17
  have eq342 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((((X2 ◇ X3) ◇ X2) ◇ X4) ◇ X1)) ◇ ((X5 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (((((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4)) ◇ X2) ◇ X3))) = X5 := superpose eq17 eq9
  have eq409 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq311 eq311
  have eq413 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose eq311 eq7
  have eq419 (X0 X1 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := superpose eq311 eq7
  have eq425 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) := superpose eq311 eq17
  have eq453 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq409 eq419
  have eq776 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq413 eq425
  have eq777 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq453 eq776
  have eq778 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((((X2 ◇ X3) ◇ X2) ◇ X4) ◇ X1)) ◇ ((X5 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X2 ◇ X3))) = X5 := superpose eq777 eq342
  have eq1049 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((((X2 ◇ X3) ◇ X2) ◇ X4) ◇ X1)) ◇ (X2 ◇ X3)) = X5 := superpose eq777 eq778
  have eq1050 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X3 ◇ X2) ◇ X4) ◇ X1)) ◇ X3) = X5 := superpose eq777 eq1049
  have eq1051 (X1 X2 X3 X4 X5 : G) : ((((X3 ◇ X2) ◇ X4) ◇ X1) ◇ X3) = X5 := superpose eq777 eq1050
  have eq1052 (X1 X3 X5 : G) : (X1 ◇ X3) = X5 := superpose eq777 eq1051
  have eq1053 (X0 X3 : G) : X0 = X3 := superpose eq1052 eq1052
  have eq1055 (X0 : G) : sK0 ≠ X0 := superpose eq1053 eq8
  subsumption eq1055 eq1053


@[equational_result]
theorem Equation24578_implies_Equation2 (G : Type*) [Magma G] (h : Equation24578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X2) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq175 eq59


@[equational_result]
theorem Equation24580_implies_Equation2 (G : Type*) [Magma G] (h : Equation24580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq7 eq10
  have eq60 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq7 eq22
  have eq76 (X0 X1 X2 : G) : (X2 ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq60 eq11
  have eq90 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := superpose eq60 eq7
  have eq174 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq90 eq90
  have eq175 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq174 eq76
  have eq177 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X0 := superpose eq175 eq90
  have eq218 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq175 eq177
  have eq219 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq175 eq218
  have eq231 (X0 X1 : G) : X0 = X1 := superpose eq219 eq175
  have eq233 (X0 : G) : sK0 ≠ X0 := superpose eq231 eq8
  subsumption eq233 eq231


@[equational_result]
theorem Equation24581_implies_Equation2 (G : Type*) [Magma G] (h : Equation24581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = X3 := superpose eq16 eq9
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq20 eq20
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq60 eq40


@[equational_result]
theorem Equation24582_implies_Equation2 (G : Type*) [Magma G] (h : Equation24582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X4 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X5)) = X2 := superpose eq10 eq10
  have eq23 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ X5)) = X4 := superpose eq14 eq9
  have eq24 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ X5)) = X4 := superpose eq14 eq23
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq51 eq29


@[equational_result]
theorem Equation24584_implies_Equation2 (G : Type*) [Magma G] (h : Equation24584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X0) := superpose eq7 eq10
  have eq21 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ ((X4 ◇ X5) ◇ X1)) = X4 := superpose eq10 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ ((X2 ◇ X3) ◇ X4))) ◇ X5) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ ((X2 ◇ X3) ◇ X4)))) ◇ X0) = X2 := superpose eq10 eq7
  have eq34 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ ((X2 ◇ X3) ◇ X4))) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ ((X2 ◇ X3) ◇ X4)))) ◇ X0) = X2 := superpose eq18 eq22
  have eq35 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq21 eq34
  have eq43 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq79 eq43


@[equational_result]
theorem Equation24585_implies_Equation2 (G : Type*) [Magma G] (h : Equation24585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X4 ◇ X5) ◇ ((X0 ◇ X3) ◇ X2))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = X4 := superpose eq16 eq9
  have eq24 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq16 eq22
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq47 eq25


@[equational_result]
theorem Equation24586_implies_Equation2 (G : Type*) [Magma G] (h : Equation24586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) = X2 := superpose eq10 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq15
  have eq61 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq143 eq61


@[equational_result]
theorem Equation24587_implies_Equation2 (G : Type*) [Magma G] (h : Equation24587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (X0 ◇ ((X3 ◇ X4) ◇ X5)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq54 (X0 X5 : G) : X0 = X5 := superpose eq7 eq17
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq158 eq54


@[equational_result]
theorem Equation24589_implies_Equation2 (G : Type*) [Magma G] (h : Equation24589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq7 eq7
  have eq17 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X4) ◇ X0)) = X4 := superpose eq9 eq9
  have eq18 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = ((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2))) ◇ X0) := superpose eq9 eq9
  have eq32 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = (((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq33 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1))) ◇ ((X1 ◇ X2) ◇ X1)) = (((((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X4) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0) := superpose eq9 eq10
  have eq41 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)))) = X2 := superpose eq10 eq7
  have eq49 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1))) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq18 eq33
  have eq53 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq41
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq17 eq17
  have eq82 (X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) = X1 := superpose eq64 eq32
  have eq83 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq82 eq53
  have eq85 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) = X3 := superpose eq83 eq9
  have eq94 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq83 eq49
  have eq102 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq83 eq85
  have eq108 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq94 eq7
  have eq118 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq94 eq108
  have eq145 (X0 X1 : G) : X0 = X1 := superpose eq118 eq102
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq145 eq8
  subsumption eq150 eq145


@[equational_result]
theorem Equation24590_implies_Equation2 (G : Type*) [Magma G] (h : Equation24590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = (((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) ◇ X3) := superpose eq7 eq11
  have eq27 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) := superpose eq7 eq9
  have eq84 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X2) = X0 := superpose eq7 eq10
  have eq169 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) := superpose eq7 eq27
  have eq346 (X0 X1 X2 X3 : G) : (X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ X2) ◇ X1))) = (((((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ X2) ◇ X1))) ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ X2) ◇ X1))) ◇ X3)) ◇ X2) := superpose eq16 eq11
  have eq359 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ X2) ◇ X1))) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ X2) ◇ X1))) ◇ X2)) ◇ X4)) ◇ X3) = X4 := superpose eq16 eq84
  have eq371 (X0 X1 X2 X3 : G) : (X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ ((X0 ◇ X2) ◇ X1))) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X2) := superpose eq169 eq346
  have eq373 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = (((((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ X0) ◇ X0) ◇ X3) := superpose eq371 eq16
  have eq418 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X2) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X2) ◇ X2)) ◇ X4)) ◇ X3) = X4 := superpose eq371 eq359
  have eq419 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = X4 := superpose eq373 eq418
  have eq436 (X0 X3 : G) : X0 = X3 := superpose eq7 eq419
  have eq632 (X0 : G) : sK0 ≠ X0 := superpose eq436 eq8
  subsumption eq632 eq436


@[equational_result]
theorem Equation24591_implies_Equation2 (G : Type*) [Magma G] (h : Equation24591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq46 eq17


@[equational_result]
theorem Equation24593_implies_Equation2 (G : Type*) [Magma G] (h : Equation24593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24594_implies_Equation2 (G : Type*) [Magma G] (h : Equation24594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24595_implies_Equation2 (G : Type*) [Magma G] (h : Equation24595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24597_implies_Equation2 (G : Type*) [Magma G] (h : Equation24597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation24598_implies_Equation2 (G : Type*) [Magma G] (h : Equation24598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation24599_implies_Equation2 (G : Type*) [Magma G] (h : Equation24599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation24601_implies_Equation2 (G : Type*) [Magma G] (h : Equation24601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24602_implies_Equation2 (G : Type*) [Magma G] (h : Equation24602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24603_implies_Equation2 (G : Type*) [Magma G] (h : Equation24603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24604_implies_Equation2 (G : Type*) [Magma G] (h : Equation24604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24607_implies_Equation2 (G : Type*) [Magma G] (h : Equation24607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X0) := superpose eq7 eq12
  have eq32 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq24 eq12
  have eq38 (X0 X2 X3 : G) : ((((X2 ◇ X0) ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq7 eq32
  have eq45 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq7 eq32
  have eq64 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = X3 := superpose eq38 eq9
  have eq70 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq45 eq64
  have eq71 (X0 X3 : G) : X0 = X3 := superpose eq7 eq70
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq101 eq71


@[equational_result]
theorem Equation24608_implies_Equation2 (G : Type*) [Magma G] (h : Equation24608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq41 eq30


@[equational_result]
theorem Equation24610_implies_Equation2 (G : Type*) [Magma G] (h : Equation24610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24611_implies_Equation2 (G : Type*) [Magma G] (h : Equation24611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24612_implies_Equation2 (G : Type*) [Magma G] (h : Equation24612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24614_implies_Equation2 (G : Type*) [Magma G] (h : Equation24614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24615_implies_Equation2 (G : Type*) [Magma G] (h : Equation24615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24616_implies_Equation2 (G : Type*) [Magma G] (h : Equation24616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24618_implies_Equation2 (G : Type*) [Magma G] (h : Equation24618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24619_implies_Equation2 (G : Type*) [Magma G] (h : Equation24619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24620_implies_Equation2 (G : Type*) [Magma G] (h : Equation24620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24621_implies_Equation2 (G : Type*) [Magma G] (h : Equation24621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24623_implies_Equation2 (G : Type*) [Magma G] (h : Equation24623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq17 eq12
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq7 eq23
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq41 eq29


@[equational_result]
theorem Equation24624_implies_Equation2 (G : Type*) [Magma G] (h : Equation24624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq53 eq36


@[equational_result]
theorem Equation24625_implies_Equation2 (G : Type*) [Magma G] (h : Equation24625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X2)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq152 eq56


@[equational_result]
theorem Equation24626_implies_Equation2 (G : Type*) [Magma G] (h : Equation24626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq30 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq50 eq30


@[equational_result]
theorem Equation24628_implies_Equation2 (G : Type*) [Magma G] (h : Equation24628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24629_implies_Equation2 (G : Type*) [Magma G] (h : Equation24629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24630_implies_Equation2 (G : Type*) [Magma G] (h : Equation24630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24631_implies_Equation2 (G : Type*) [Magma G] (h : Equation24631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24633_implies_Equation2 (G : Type*) [Magma G] (h : Equation24633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24634_implies_Equation2 (G : Type*) [Magma G] (h : Equation24634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24635_implies_Equation2 (G : Type*) [Magma G] (h : Equation24635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24636_implies_Equation2 (G : Type*) [Magma G] (h : Equation24636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24638_implies_Equation2 (G : Type*) [Magma G] (h : Equation24638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24639_implies_Equation2 (G : Type*) [Magma G] (h : Equation24639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24640_implies_Equation2 (G : Type*) [Magma G] (h : Equation24640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24641_implies_Equation2 (G : Type*) [Magma G] (h : Equation24641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24643_implies_Equation2 (G : Type*) [Magma G] (h : Equation24643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24644_implies_Equation2 (G : Type*) [Magma G] (h : Equation24644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24645_implies_Equation2 (G : Type*) [Magma G] (h : Equation24645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24646_implies_Equation2 (G : Type*) [Magma G] (h : Equation24646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24647_implies_Equation2 (G : Type*) [Magma G] (h : Equation24647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24650_implies_Equation2 (G : Type*) [Magma G] (h : Equation24650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq10
  have eq14 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X3))) := superpose eq7 eq10
  have eq21 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq10
  have eq39 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = (((X3 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) ◇ X0) := superpose eq9 eq10
  have eq45 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq14 eq39
  have eq47 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq9 eq21
  have eq49 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq21 eq9
  have eq51 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq21 eq7
  have eq61 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq51 eq49
  have eq62 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq61 eq47
  have eq91 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = (((X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ X0) := superpose eq51 eq10
  have eq94 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq51 eq9
  have eq162 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq94 eq94
  have eq191 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq162 eq45
  have eq192 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq162 eq91
  have eq209 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X0)) := superpose eq192 eq11
  have eq213 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq192 eq62
  have eq219 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq192 eq191
  have eq260 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq94 eq209
  have eq276 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq260 eq213
  have eq278 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X2) := superpose eq276 eq219
  have eq279 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X0))) = X3 := superpose eq278 eq9
  have eq285 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X2 := superpose eq278 eq162
  have eq299 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) = X3 := superpose eq278 eq279
  have eq300 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X3 := superpose eq260 eq299
  have eq305 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq300 eq285
  have eq342 (X0 X1 : G) : X0 = X1 := superpose eq300 eq305
  have eq353 (X0 : G) : sK0 ≠ X0 := superpose eq342 eq8
  subsumption eq353 eq342


@[equational_result]
theorem Equation24651_implies_Equation2 (G : Type*) [Magma G] (h : Equation24651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq134 eq50


@[equational_result]
theorem Equation24653_implies_Equation2 (G : Type*) [Magma G] (h : Equation24653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X3) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X2) ◇ X2) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq12
  have eq19 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) := superpose eq7 eq12
  have eq21 (X0 X1 X2 : G) : (X2 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq12 eq12
  have eq43 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X3 ◇ X2) ◇ X2)) ◇ X2) = (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq19 eq19
  have eq58 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq19
  have eq111 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)))) = ((X4 ◇ ((X4 ◇ (X3 ◇ ((X3 ◇ X1) ◇ X1))) ◇ (X3 ◇ ((X3 ◇ X1) ◇ X1)))) ◇ (X3 ◇ ((X3 ◇ X1) ◇ X1))) := superpose eq9 eq19
  have eq114 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) = (((X2 ◇ X3) ◇ X3) ◇ X2) := superpose eq19 eq58
  have eq117 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)))) = ((((X3 ◇ ((X3 ◇ X1) ◇ X1)) ◇ X4) ◇ X4) ◇ (X3 ◇ ((X3 ◇ X1) ◇ X1))) := superpose eq9 eq58
  have eq156 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = (X1 ◇ X1) := superpose eq58 eq7
  have eq176 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq156 eq17
  have eq186 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) = (X2 ◇ X2) := superpose eq176 eq114
  have eq213 (X2 X3 : G) : ((X3 ◇ ((X3 ◇ X2) ◇ X2)) ◇ X2) = (X2 ◇ X2) := superpose eq186 eq43
  have eq259 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))) = (((((X4 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ X5) ◇ X5) ◇ (X4 ◇ ((X4 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)))) := superpose eq11 eq11
  have eq270 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ X4) = ((((((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)))) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq11 eq11
  have eq271 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4) ◇ X4) ◇ (((X1 ◇ X3) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq7 eq11
  have eq300 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = ((X4 ◇ ((X4 ◇ X1) ◇ X1)) ◇ X1) := superpose eq11 eq19
  have eq316 (X0 X1 X2 X3 : G) : (X3 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = X1 := superpose eq11 eq10
  have eq355 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq213 eq300
  have eq369 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq316 eq355
  have eq378 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq369 eq176
  have eq417 (X0 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq378 eq58
  have eq420 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq417 eq12
  have eq423 (X0 X1 X2 : G) : (X2 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) = ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq417 eq21
  have eq490 (X0 X1 X2 : G) : (X2 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq369 eq423
  have eq491 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq417 eq490
  have eq506 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)))) = ((X4 ◇ ((X4 ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1))) ◇ ((X3 ◇ X1) ◇ X1)) := superpose eq491 eq111
  have eq508 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)))) = (((((X3 ◇ X1) ◇ X1) ◇ X4) ◇ X4) ◇ ((X3 ◇ X1) ◇ X1)) := superpose eq491 eq117
  have eq510 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) = (((((X4 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ X5) ◇ X5) ◇ (X4 ◇ ((X4 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)))) := superpose eq491 eq259
  have eq512 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ X4) = ((((((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)))) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq491 eq270
  have eq513 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X4) ◇ (((X1 ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq491 eq271
  have eq549 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)))) = (((X4 ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1)) := superpose eq491 eq506
  have eq550 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) = (((X4 ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1)) := superpose eq491 eq549
  have eq551 (X0 X1 X2 X3 X4 : G) : (((((X3 ◇ X1) ◇ X1) ◇ X4) ◇ X4) ◇ ((X3 ◇ X1) ◇ X1)) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq491 eq508
  have eq553 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ X0) ◇ X0)) = (((((X4 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ X5) ◇ X5) ◇ ((X4 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3))) := superpose eq491 eq510
  have eq554 (X0 X2 X3 X4 X5 : G) : (((((X4 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ X5) ◇ X5) ◇ ((X4 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) ◇ ((((X2 ◇ X0) ◇ X0) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq553
  have eq556 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ X4) = ((((((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq491 eq512
  have eq557 (X0 X1 X2 X4 : G) : ((X2 ◇ X4) ◇ X4) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq378 eq556
  have eq558 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X4) ◇ X4) ◇ X0) := superpose eq7 eq513
  have eq559 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = X0 := superpose eq420 eq558
  have eq568 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ X1) ◇ X1)) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq559 eq551
  have eq569 (X2 X4 X5 : G) : (((((X4 ◇ X2) ◇ X2) ◇ X5) ◇ X5) ◇ ((X4 ◇ X2) ◇ X2)) = X2 := superpose eq559 eq554
  have eq573 (X2 X4 : G) : (X4 ◇ ((X4 ◇ X2) ◇ X2)) = X2 := superpose eq559 eq569
  have eq574 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) = X1 := superpose eq573 eq568
  have eq578 (X1 X3 X4 : G) : (((X4 ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1)) = X1 := superpose eq574 eq550
  have eq579 (X2 X4 : G) : ((X2 ◇ X4) ◇ X4) = X2 := superpose eq578 eq557
  have eq580 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq579 eq7
  have eq599 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq579 eq580
  have eq600 (X2 X4 : G) : (X4 ◇ X4) = X2 := superpose eq599 eq579
  have eq603 (X0 X1 : G) : X0 = X1 := superpose eq599 eq600
  have eq608 (X0 : G) : sK0 ≠ X0 := superpose eq603 eq8
  subsumption eq608 eq603


@[equational_result]
theorem Equation24655_implies_Equation2 (G : Type*) [Magma G] (h : Equation24655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (((X1 ◇ X2) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq157 eq61


@[equational_result]
theorem Equation24658_implies_Equation2 (G : Type*) [Magma G] (h : Equation24658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X3) ◇ X3)) = (((X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)))) := superpose eq9 eq7
  have eq42 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X3)) = ((X2 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)))) ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq10 eq9
  have eq49 (X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X3)) = ((X2 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq17 eq42
  have eq50 (X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X3)) = X2 := superpose eq9 eq49
  have eq53 (X0 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X3 := superpose eq50 eq9
  have eq79 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq50 eq53
  have eq103 (X0 X2 : G) : X0 = X2 := superpose eq79 eq79
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq103 eq8
  subsumption eq105 eq103


@[equational_result]
theorem Equation24659_implies_Equation2 (G : Type*) [Magma G] (h : Equation24659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (((X1 ◇ X2) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq173 eq58


@[equational_result]
theorem Equation24661_implies_Equation2 (G : Type*) [Magma G] (h : Equation24661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X3) ◇ X1)) ◇ ((X4 ◇ X5) ◇ ((X1 ◇ X2) ◇ X2))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1)))) = X3 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq10 eq10
  have eq25 (X0 X1 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X1) = X4 := superpose eq20 eq9
  have eq30 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq20 eq25
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq7 eq30
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq44 eq31


@[equational_result]
theorem Equation24662_implies_Equation2 (G : Type*) [Magma G] (h : Equation24662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X4) = (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq7 eq10
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq166 eq65


@[equational_result]
theorem Equation24663_implies_Equation2 (G : Type*) [Magma G] (h : Equation24663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) = X2 := superpose eq10 eq10
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq17
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq128 eq42


@[equational_result]
theorem Equation24664_implies_Equation2 (G : Type*) [Magma G] (h : Equation24664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X6)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq54 (X0 X5 : G) : X0 = X5 := superpose eq7 eq17
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq158 eq54


@[equational_result]
theorem Equation24667_implies_Equation2 (G : Type*) [Magma G] (h : Equation24667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (((((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) ◇ X2) = X3 := superpose eq11 eq11
  have eq37 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X3) ◇ X0)) = ((X0 ◇ X3) ◇ (X2 ◇ X3)) := superpose eq11 eq10
  have eq100 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X2 ◇ X3) ◇ X4)) = ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) ◇ ((X1 ◇ X4) ◇ X3)) := superpose eq37 eq37
  have eq104 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ (X4 ◇ X2)) = ((((((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X4) ◇ (X0 ◇ X3)) := superpose eq11 eq37
  have eq161 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (X2 ◇ X3)) ◇ (((X1 ◇ X3) ◇ X4) ◇ (X2 ◇ X3))) = X4 := superpose eq37 eq7
  have eq173 (X0 X2 X3 : G) : (((X3 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2)) ◇ X2) = X3 := superpose eq104 eq29
  have eq195 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) ◇ X3) := superpose eq7 eq173
  have eq211 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq7 eq173
  have eq233 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq211 eq7
  have eq235 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq211 eq10
  have eq348 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq211 eq235
  have eq352 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) := superpose eq348 eq195
  have eq357 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((X1 ◇ X0) ◇ X2) ◇ X3) := superpose eq211 eq352
  have eq371 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X3) ◇ X4)) = X4 := superpose eq357 eq161
  have eq373 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X2 ◇ X3) ◇ X4)) = (((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X4) ◇ X3)) := superpose eq357 eq100
  have eq403 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) ◇ ((X1 ◇ X3) ◇ X4)) = X4 := superpose eq357 eq371
  have eq404 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) = X4 := superpose eq357 eq403
  have eq405 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X2 ◇ X3) ◇ X4)) = X3 := superpose eq404 eq373
  have eq407 (X2 X3 : G) : (X3 ◇ X2) = X3 := superpose eq405 eq173
  have eq417 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X0 := superpose eq407 eq233
  have eq468 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq407 eq417
  have eq469 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq407 eq468
  have eq479 (X0 X2 : G) : X0 = X2 := superpose eq469 eq469
  have eq481 (X0 : G) : sK0 ≠ X0 := superpose eq479 eq8
  subsumption eq481 eq479


@[equational_result]
theorem Equation24668_implies_Equation2 (G : Type*) [Magma G] (h : Equation24668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq43 eq19


@[equational_result]
theorem Equation24670_implies_Equation2 (G : Type*) [Magma G] (h : Equation24670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24671_implies_Equation2 (G : Type*) [Magma G] (h : Equation24671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24672_implies_Equation2 (G : Type*) [Magma G] (h : Equation24672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24674_implies_Equation2 (G : Type*) [Magma G] (h : Equation24674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation24675_implies_Equation2 (G : Type*) [Magma G] (h : Equation24675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation24676_implies_Equation2 (G : Type*) [Magma G] (h : Equation24676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation24678_implies_Equation2 (G : Type*) [Magma G] (h : Equation24678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24679_implies_Equation2 (G : Type*) [Magma G] (h : Equation24679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24680_implies_Equation2 (G : Type*) [Magma G] (h : Equation24680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24681_implies_Equation2 (G : Type*) [Magma G] (h : Equation24681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24684_implies_Equation2 (G : Type*) [Magma G] (h : Equation24684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3) = X2 := superpose eq11 eq11
  have eq100 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq13
  have eq162 (X0 X1 : G) : X0 = X1 := superpose eq7 eq100
  have eq251 (X0 : G) : sK0 ≠ X0 := superpose eq162 eq8
  subsumption eq251 eq162


@[equational_result]
theorem Equation24685_implies_Equation2 (G : Type*) [Magma G] (h : Equation24685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ X4) = (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X0 ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = X3 := superpose eq11 eq10
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation24687_implies_Equation2 (G : Type*) [Magma G] (h : Equation24687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24688_implies_Equation2 (G : Type*) [Magma G] (h : Equation24688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24689_implies_Equation2 (G : Type*) [Magma G] (h : Equation24689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24691_implies_Equation2 (G : Type*) [Magma G] (h : Equation24691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24692_implies_Equation2 (G : Type*) [Magma G] (h : Equation24692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24693_implies_Equation2 (G : Type*) [Magma G] (h : Equation24693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24695_implies_Equation2 (G : Type*) [Magma G] (h : Equation24695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24696_implies_Equation2 (G : Type*) [Magma G] (h : Equation24696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24697_implies_Equation2 (G : Type*) [Magma G] (h : Equation24697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24698_implies_Equation2 (G : Type*) [Magma G] (h : Equation24698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24700_implies_Equation2 (G : Type*) [Magma G] (h : Equation24700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq60 eq25


@[equational_result]
theorem Equation24701_implies_Equation2 (G : Type*) [Magma G] (h : Equation24701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ X0) ◇ X4) = (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq7 eq10
  have eq39 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq25 eq11
  have eq45 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) = X0 := superpose eq39 eq7
  have eq60 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = X0 := superpose eq39 eq45
  have eq61 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq39 eq60
  have eq62 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq39 eq61
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq62 eq62
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq65 eq63


@[equational_result]
theorem Equation24702_implies_Equation2 (G : Type*) [Magma G] (h : Equation24702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq50 eq30


@[equational_result]
theorem Equation24703_implies_Equation2 (G : Type*) [Magma G] (h : Equation24703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq30 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq50 eq30


@[equational_result]
theorem Equation24705_implies_Equation2 (G : Type*) [Magma G] (h : Equation24705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24706_implies_Equation2 (G : Type*) [Magma G] (h : Equation24706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24707_implies_Equation2 (G : Type*) [Magma G] (h : Equation24707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24708_implies_Equation2 (G : Type*) [Magma G] (h : Equation24708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24710_implies_Equation2 (G : Type*) [Magma G] (h : Equation24710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24711_implies_Equation2 (G : Type*) [Magma G] (h : Equation24711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24712_implies_Equation2 (G : Type*) [Magma G] (h : Equation24712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24713_implies_Equation2 (G : Type*) [Magma G] (h : Equation24713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24715_implies_Equation2 (G : Type*) [Magma G] (h : Equation24715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24716_implies_Equation2 (G : Type*) [Magma G] (h : Equation24716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24717_implies_Equation2 (G : Type*) [Magma G] (h : Equation24717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24718_implies_Equation2 (G : Type*) [Magma G] (h : Equation24718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24720_implies_Equation2 (G : Type*) [Magma G] (h : Equation24720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24721_implies_Equation2 (G : Type*) [Magma G] (h : Equation24721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24722_implies_Equation2 (G : Type*) [Magma G] (h : Equation24722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24723_implies_Equation2 (G : Type*) [Magma G] (h : Equation24723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24724_implies_Equation2 (G : Type*) [Magma G] (h : Equation24724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24726_implies_Equation2 (G : Type*) [Magma G] (h : Equation24726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X4 ◇ X4) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq149 eq45


@[equational_result]
theorem Equation24727_implies_Equation2 (G : Type*) [Magma G] (h : Equation24727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X4 ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X0) = X5 := superpose eq10 eq9
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq45 eq18


@[equational_result]
theorem Equation24728_implies_Equation2 (G : Type*) [Magma G] (h : Equation24728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X4 ◇ X4) ◇ ((X0 ◇ X0) ◇ X3))) = X4 := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq38 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq27 eq10
  have eq45 (X0 X2 : G) : X0 = X2 := superpose eq7 eq38
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq123 eq45


@[equational_result]
theorem Equation24729_implies_Equation2 (G : Type*) [Magma G] (h : Equation24729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ ((X5 ◇ X5) ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation24731_implies_Equation2 (G : Type*) [Magma G] (h : Equation24731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)))) = X2 := superpose eq10 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq14
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq147 eq59


@[equational_result]
theorem Equation24732_implies_Equation2 (G : Type*) [Magma G] (h : Equation24732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ X3)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X6 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X6)) = X2 := superpose eq7 eq10
  have eq23 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X0) = X5 := superpose eq13 eq9
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq10 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation24733_implies_Equation2 (G : Type*) [Magma G] (h : Equation24733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3))) = X4 := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ ((X3 ◇ X4) ◇ X5)) ◇ X1)) ◇ X0) = X6 := superpose eq9 eq7
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X0)) = X3 := superpose eq7 eq10
  have eq51 (X0 X6 : G) : (X0 ◇ X0) = X6 := superpose eq36 eq23
  have eq61 (X0 X2 : G) : X0 = X2 := superpose eq7 eq51
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq166 eq61


@[equational_result]
theorem Equation24734_implies_Equation2 (G : Type*) [Magma G] (h : Equation24734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ ((X6 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X7)) = X6 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ (X1 ◇ X2)) ◇ X6)) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X7 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X7)) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ (X1 ◇ X7)) = X6 := superpose eq13 eq9
  have eq32 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq54 eq32


@[equational_result]
theorem Equation24736_implies_Equation2 (G : Type*) [Magma G] (h : Equation24736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ ((X0 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X3))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ X3) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 X4 X5 : G) : ((X0 ◇ X4) ◇ X1) = X5 := superpose eq15 eq9
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq51 eq29


@[equational_result]
theorem Equation24737_implies_Equation2 (G : Type*) [Magma G] (h : Equation24737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X4 ◇ X3) ◇ X3)) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X0) = X5 := superpose eq10 eq9
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq49 eq20


@[equational_result]
theorem Equation24738_implies_Equation2 (G : Type*) [Magma G] (h : Equation24738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ X3) ◇ ((X0 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) = X2 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (((X4 ◇ X2) ◇ X5) ◇ X3))) ◇ X0) = X4 := superpose eq10 eq7
  have eq27 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq16 eq22
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq27
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq147 eq57


@[equational_result]
theorem Equation24739_implies_Equation2 (G : Type*) [Magma G] (h : Equation24739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ ((X6 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X7)) = X6 := superpose eq7 eq7
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ ((X5 ◇ X3) ◇ X6)) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ (X0 ◇ X7)) = X6 := superpose eq10 eq9
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq51 eq31


@[equational_result]
theorem Equation24741_implies_Equation2 (G : Type*) [Magma G] (h : Equation24741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ X4) ◇ ((X1 ◇ X2) ◇ X3))) = X5 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq9 eq9
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq166 eq53


@[equational_result]
theorem Equation24742_implies_Equation2 (G : Type*) [Magma G] (h : Equation24742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ X4) ◇ ((X0 ◇ X3) ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X3)) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) = X3 := superpose eq7 eq10
  have eq24 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X0) = X5 := superpose eq15 eq9
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq24
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq53 eq31


@[equational_result]
theorem Equation24743_implies_Equation2 (G : Type*) [Magma G] (h : Equation24743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X5 ◇ X4) ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X4 ◇ ((X0 ◇ X3) ◇ X3)) ◇ ((X0 ◇ X3) ◇ X3))) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq9 eq10
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)))) = X1 := superpose eq10 eq10
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X0 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)))) = X2 := superpose eq10 eq9
  have eq33 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = (((X3 ◇ X4) ◇ X2) ◇ (((X3 ◇ X4) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2)))) := superpose eq7 eq20
  have eq39 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq20
  have eq41 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = (X0 ◇ X0) := superpose eq10 eq20
  have eq63 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))) = X2 := superpose eq41 eq25
  have eq65 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq41 eq21
  have eq75 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = (((X3 ◇ X4) ◇ X2) ◇ (((X3 ◇ X4) ◇ X2) ◇ (X0 ◇ X0))) := superpose eq41 eq33
  have eq80 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq65 eq75
  have eq84 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq80 eq41
  have eq86 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X2 := superpose eq84 eq63
  have eq92 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq86 eq39
  have eq94 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X3) = X0 := superpose eq92 eq7
  have eq99 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq92 eq94
  have eq101 (X0 X2 : G) : X0 = X2 := superpose eq99 eq99
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq101 eq8
  subsumption eq103 eq101


@[equational_result]
theorem Equation24744_implies_Equation2 (G : Type*) [Magma G] (h : Equation24744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X5) = (((X1 ◇ X2) ◇ X3) ◇ X0) := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq35
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq133 eq57


@[equational_result]
theorem Equation24746_implies_Equation2 (G : Type*) [Magma G] (h : Equation24746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ ((X6 ◇ X7) ◇ ((X1 ◇ X2) ◇ X3))) = X6 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 X5 X6 : G) : ((X0 ◇ X5) ◇ X1) = X6 := superpose eq15 eq9
  have eq28 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq50 eq28


@[equational_result]
theorem Equation24747_implies_Equation2 (G : Type*) [Magma G] (h : Equation24747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ ((X6 ◇ X7) ◇ ((X0 ◇ X4) ◇ X2))) = X6 := superpose eq7 eq7
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ X3)) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X0) = X6 := superpose eq10 eq9
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation24748_implies_Equation2 (G : Type*) [Magma G] (h : Equation24748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ ((X0 ◇ X4) ◇ X3))) = X5 := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) = X3 := superpose eq7 eq10
  have eq43 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq29 eq10
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq7 eq43
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq105 eq51


@[equational_result]
theorem Equation24749_implies_Equation2 (G : Type*) [Magma G] (h : Equation24749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ X6)) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) = X2 := superpose eq10 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq15
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq122 eq39


@[equational_result]
theorem Equation24750_implies_Equation2 (G : Type*) [Magma G] (h : Equation24750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X6 X7 X8 : G) : (X0 ◇ ((X6 ◇ X7) ◇ X8)) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq36 (X0 X6 : G) : X0 = X6 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation24752_implies_Equation2 (G : Type*) [Magma G] (h : Equation24752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq10 eq10
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq128 eq42


@[equational_result]
theorem Equation24753_implies_Equation2 (G : Type*) [Magma G] (h : Equation24753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X1 ◇ X2) ◇ X3) ◇ X5) ◇ ((X1 ◇ X0) ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X5 X6 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X6)) = X5 := superpose eq7 eq10
  have eq23 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X0) = X5 := superpose eq13 eq9
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq10 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation24754_implies_Equation2 (G : Type*) [Magma G] (h : Equation24754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X1 ◇ X2) ◇ X3) ◇ X5) ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ ((X1 ◇ X0) ◇ X3))) = X4 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ X6) ◇ ((((X3 ◇ X4) ◇ X5) ◇ X0) ◇ X2))) = X6 := superpose eq9 eq7
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X5) ◇ X0)) = X5 := superpose eq7 eq10
  have eq51 (X0 X6 : G) : (X0 ◇ X0) = X6 := superpose eq36 eq24
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq51
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq139 eq57


@[equational_result]
theorem Equation24755_implies_Equation2 (G : Type*) [Magma G] (h : Equation24755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X5 := superpose eq7 eq7
  have eq35 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation24757_implies_Equation2 (G : Type*) [Magma G] (h : Equation24757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24758_implies_Equation2 (G : Type*) [Magma G] (h : Equation24758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24759_implies_Equation2 (G : Type*) [Magma G] (h : Equation24759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24760_implies_Equation2 (G : Type*) [Magma G] (h : Equation24760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24762_implies_Equation2 (G : Type*) [Magma G] (h : Equation24762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation24763_implies_Equation2 (G : Type*) [Magma G] (h : Equation24763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24764_implies_Equation2 (G : Type*) [Magma G] (h : Equation24764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation24765_implies_Equation2 (G : Type*) [Magma G] (h : Equation24765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation24767_implies_Equation2 (G : Type*) [Magma G] (h : Equation24767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24768_implies_Equation2 (G : Type*) [Magma G] (h : Equation24768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24769_implies_Equation2 (G : Type*) [Magma G] (h : Equation24769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24770_implies_Equation2 (G : Type*) [Magma G] (h : Equation24770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24772_implies_Equation2 (G : Type*) [Magma G] (h : Equation24772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24773_implies_Equation2 (G : Type*) [Magma G] (h : Equation24773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24774_implies_Equation2 (G : Type*) [Magma G] (h : Equation24774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24775_implies_Equation2 (G : Type*) [Magma G] (h : Equation24775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24776_implies_Equation2 (G : Type*) [Magma G] (h : Equation24776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24778_implies_Equation2 (G : Type*) [Magma G] (h : Equation24778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X2 ◇ X0) ◇ X1) ◇ X5) ◇ ((X1 ◇ X2) ◇ X3))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq23 (X0 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ X2) = X5 := superpose eq15 eq9
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq51 eq29


@[equational_result]
theorem Equation24779_implies_Equation2 (G : Type*) [Magma G] (h : Equation24779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X5) ◇ ((X2 ◇ X0) ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X0) = X5 := superpose eq7 eq9
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation24780_implies_Equation2 (G : Type*) [Magma G] (h : Equation24780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((((X2 ◇ X0) ◇ X3) ◇ X5) ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ ((X2 ◇ X0) ◇ X3))) = X4 := superpose eq7 eq7
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq9 eq10
  have eq47 (X0 X2 : G) : X0 = X2 := superpose eq7 eq39
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq124 eq47


@[equational_result]
theorem Equation24781_implies_Equation2 (G : Type*) [Magma G] (h : Equation24781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) = X5 := superpose eq7 eq7
  have eq34 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq54 eq34


@[equational_result]
theorem Equation24783_implies_Equation2 (G : Type*) [Magma G] (h : Equation24783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24784_implies_Equation2 (G : Type*) [Magma G] (h : Equation24784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24785_implies_Equation2 (G : Type*) [Magma G] (h : Equation24785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24786_implies_Equation2 (G : Type*) [Magma G] (h : Equation24786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24788_implies_Equation2 (G : Type*) [Magma G] (h : Equation24788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24789_implies_Equation2 (G : Type*) [Magma G] (h : Equation24789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24790_implies_Equation2 (G : Type*) [Magma G] (h : Equation24790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24791_implies_Equation2 (G : Type*) [Magma G] (h : Equation24791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24793_implies_Equation2 (G : Type*) [Magma G] (h : Equation24793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24794_implies_Equation2 (G : Type*) [Magma G] (h : Equation24794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24795_implies_Equation2 (G : Type*) [Magma G] (h : Equation24795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24796_implies_Equation2 (G : Type*) [Magma G] (h : Equation24796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24798_implies_Equation2 (G : Type*) [Magma G] (h : Equation24798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24799_implies_Equation2 (G : Type*) [Magma G] (h : Equation24799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24800_implies_Equation2 (G : Type*) [Magma G] (h : Equation24800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24801_implies_Equation2 (G : Type*) [Magma G] (h : Equation24801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24802_implies_Equation2 (G : Type*) [Magma G] (h : Equation24802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24804_implies_Equation2 (G : Type*) [Magma G] (h : Equation24804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X3 ◇ X0) ◇ X1) ◇ X4) ◇ (X1 ◇ X2))) = X4 := superpose eq7 eq7
  have eq39 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq39
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq137 eq50


@[equational_result]
theorem Equation24805_implies_Equation2 (G : Type*) [Magma G] (h : Equation24805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X4 ◇ X5) ◇ ((X3 ◇ X0) ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((((X3 ◇ X0) ◇ X2) ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X2)) = X5 := superpose eq10 eq10
  have eq26 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X0) = X5 := superpose eq16 eq9
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq26
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq54 eq33


@[equational_result]
theorem Equation24806_implies_Equation2 (G : Type*) [Magma G] (h : Equation24806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq32 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq7 eq12
  have eq42 (X0 X2 : G) : X0 = X2 := superpose eq7 eq32
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq99 eq42


@[equational_result]
theorem Equation24807_implies_Equation2 (G : Type*) [Magma G] (h : Equation24807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X5 := superpose eq7 eq7
  have eq35 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation24809_implies_Equation2 (G : Type*) [Magma G] (h : Equation24809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24810_implies_Equation2 (G : Type*) [Magma G] (h : Equation24810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24811_implies_Equation2 (G : Type*) [Magma G] (h : Equation24811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24812_implies_Equation2 (G : Type*) [Magma G] (h : Equation24812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24814_implies_Equation2 (G : Type*) [Magma G] (h : Equation24814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24815_implies_Equation2 (G : Type*) [Magma G] (h : Equation24815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24816_implies_Equation2 (G : Type*) [Magma G] (h : Equation24816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24817_implies_Equation2 (G : Type*) [Magma G] (h : Equation24817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24819_implies_Equation2 (G : Type*) [Magma G] (h : Equation24819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24820_implies_Equation2 (G : Type*) [Magma G] (h : Equation24820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24821_implies_Equation2 (G : Type*) [Magma G] (h : Equation24821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24822_implies_Equation2 (G : Type*) [Magma G] (h : Equation24822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24824_implies_Equation2 (G : Type*) [Magma G] (h : Equation24824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24825_implies_Equation2 (G : Type*) [Magma G] (h : Equation24825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24826_implies_Equation2 (G : Type*) [Magma G] (h : Equation24826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24827_implies_Equation2 (G : Type*) [Magma G] (h : Equation24827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24828_implies_Equation2 (G : Type*) [Magma G] (h : Equation24828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24830_implies_Equation2 (G : Type*) [Magma G] (h : Equation24830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ ((X6 ◇ X7) ◇ ((X1 ◇ X2) ◇ X3))) = X7 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X1 ◇ X2))) = X6 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq23 (X0 X2 X5 X7 : G) : ((X0 ◇ X5) ◇ X2) = X7 := superpose eq15 eq9
  have eq28 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq50 eq28


@[equational_result]
theorem Equation24831_implies_Equation2 (G : Type*) [Magma G] (h : Equation24831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 X6 X7 : G) : ((X0 ◇ X5) ◇ ((X6 ◇ X7) ◇ ((X4 ◇ X0) ◇ X2))) = X7 := superpose eq7 eq7
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ X3)) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : ((X0 ◇ X5) ◇ X0) = X7 := superpose eq10 eq9
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation24832_implies_Equation2 (G : Type*) [Magma G] (h : Equation24832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ ((X4 ◇ X0) ◇ X3))) = X6 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq42 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq29 eq12
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq7 eq42
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq126 eq48


@[equational_result]
theorem Equation24833_implies_Equation2 (G : Type*) [Magma G] (h : Equation24833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X5 := superpose eq7 eq7
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation24834_implies_Equation2 (G : Type*) [Magma G] (h : Equation24834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X6 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X6 := superpose eq7 eq7
  have eq29 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation24836_implies_Equation2 (G : Type*) [Magma G] (h : Equation24836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24837_implies_Equation2 (G : Type*) [Magma G] (h : Equation24837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24838_implies_Equation2 (G : Type*) [Magma G] (h : Equation24838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24839_implies_Equation2 (G : Type*) [Magma G] (h : Equation24839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24840_implies_Equation2 (G : Type*) [Magma G] (h : Equation24840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X1) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24842_implies_Equation2 (G : Type*) [Magma G] (h : Equation24842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24843_implies_Equation2 (G : Type*) [Magma G] (h : Equation24843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24844_implies_Equation2 (G : Type*) [Magma G] (h : Equation24844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24845_implies_Equation2 (G : Type*) [Magma G] (h : Equation24845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24846_implies_Equation2 (G : Type*) [Magma G] (h : Equation24846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X2) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24848_implies_Equation2 (G : Type*) [Magma G] (h : Equation24848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24849_implies_Equation2 (G : Type*) [Magma G] (h : Equation24849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24850_implies_Equation2 (G : Type*) [Magma G] (h : Equation24850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation24851_implies_Equation2 (G : Type*) [Magma G] (h : Equation24851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24852_implies_Equation2 (G : Type*) [Magma G] (h : Equation24852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X3) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24854_implies_Equation2 (G : Type*) [Magma G] (h : Equation24854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24855_implies_Equation2 (G : Type*) [Magma G] (h : Equation24855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24856_implies_Equation2 (G : Type*) [Magma G] (h : Equation24856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24857_implies_Equation2 (G : Type*) [Magma G] (h : Equation24857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24858_implies_Equation2 (G : Type*) [Magma G] (h : Equation24858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24860_implies_Equation2 (G : Type*) [Magma G] (h : Equation24860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X5) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24861_implies_Equation2 (G : Type*) [Magma G] (h : Equation24861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X5) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24862_implies_Equation2 (G : Type*) [Magma G] (h : Equation24862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X5) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24863_implies_Equation2 (G : Type*) [Magma G] (h : Equation24863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X5) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24864_implies_Equation2 (G : Type*) [Magma G] (h : Equation24864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X5) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation24865_implies_Equation2 (G : Type*) [Magma G] (h : Equation24865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X5) ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25071_implies_Equation2 (G : Type*) [Magma G] (h : Equation25071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq7
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq10 eq13
  have eq21 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq10 eq13
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq10
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq21 eq23
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq24 eq19
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq24 eq27
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq16 eq31
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq40 eq32


@[equational_result]
theorem Equation25074_implies_Equation2 (G : Type*) [Magma G] (h : Equation25074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq7 eq15
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq98 eq31


@[equational_result]
theorem Equation25076_implies_Equation2 (G : Type*) [Magma G] (h : Equation25076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq11 eq10
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq38 eq34


@[equational_result]
theorem Equation25077_implies_Equation2 (G : Type*) [Magma G] (h : Equation25077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq156 eq57


@[equational_result]
theorem Equation25078_implies_Equation2 (G : Type*) [Magma G] (h : Equation25078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation25081_implies_Equation2 (G : Type*) [Magma G] (h : Equation25081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq7
  have eq19 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq10 eq13
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq10
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq19 eq21
  have eq25 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq23 eq10
  have eq33 (X0 X1 : G) : X0 = X1 := superpose eq25 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq46 eq33


@[equational_result]
theorem Equation25084_implies_Equation2 (G : Type*) [Magma G] (h : Equation25084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq7 eq16
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq101 eq35


@[equational_result]
theorem Equation25086_implies_Equation2 (G : Type*) [Magma G] (h : Equation25086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X0) = X3 := superpose eq7 eq7
  have eq48 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq11 eq11
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq7 eq48
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq187 eq70


@[equational_result]
theorem Equation25088_implies_Equation2 (G : Type*) [Magma G] (h : Equation25088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation25090_implies_Equation2 (G : Type*) [Magma G] (h : Equation25090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))))) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq10 eq10
  have eq17 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0) = X0 := superpose eq10 eq7
  have eq19 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq7
  have eq25 (X0 X1 X4 : G) : (X1 ◇ X0) = ((X4 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X4)) := superpose eq10 eq9
  have eq86 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq10 eq16
  have eq101 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) := superpose eq16 eq17
  have eq107 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq19 eq19
  have eq132 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq86 eq107
  have eq168 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X0 := superpose eq132 eq7
  have eq179 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq132 eq7
  have eq193 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq7 eq25
  have eq249 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ X0) := superpose eq168 eq9
  have eq275 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq132 eq249
  have eq276 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq132 eq275
  have eq281 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq276 eq179
  have eq332 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ (X0 ◇ X3))) = ((X0 ◇ X0) ◇ X0) := superpose eq18 eq9
  have eq359 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq132 eq332
  have eq360 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq132 eq359
  have eq384 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq281 eq281
  have eq411 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq281 eq384
  have eq412 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq276 eq411
  have eq478 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq412 eq193
  have eq486 (X0 X1 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq412 eq360
  have eq541 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = X0 := superpose eq412 eq486
  have eq542 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq541 eq101
  have eq544 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq132 eq542
  have eq642 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq412 eq17
  have eq672 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq544 eq642
  have eq675 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq672 eq478
  have eq684 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq672 eq675
  have eq685 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq672 eq684
  have eq686 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq672 eq685
  have eq688 (X0 X1 : G) : X0 = X1 := superpose eq686 eq672
  have eq690 (X0 : G) : sK0 ≠ X0 := superpose eq688 eq8
  subsumption eq690 eq688


@[equational_result]
theorem Equation25091_implies_Equation2 (G : Type*) [Magma G] (h : Equation25091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) := superpose eq9 eq10
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq11
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq11
  have eq19 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq16 eq12
  have eq20 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq16 eq19
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq20 eq14
  have eq25 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq20 eq22
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq34 eq26


@[equational_result]
theorem Equation25092_implies_Equation2 (G : Type*) [Magma G] (h : Equation25092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq10 eq7
  have eq19 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq10 eq13
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq13 eq10
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq19 eq21
  have eq25 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq23 eq10
  have eq33 (X0 X1 : G) : X0 = X1 := superpose eq25 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq46 eq33


@[equational_result]
theorem Equation25094_implies_Equation2 (G : Type*) [Magma G] (h : Equation25094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)) ◇ (X3 ◇ (X3 ◇ X4))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) ◇ (X0 ◇ (X0 ◇ X4))) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) ◇ (X0 ◇ (X0 ◇ X4))))) = X1 := superpose eq10 eq7
  have eq20 (X0 X1 X5 : G) : ((X5 ◇ (X0 ◇ X1)) ◇ (X5 ◇ X5)) = X0 := superpose eq10 eq9
  have eq33 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = ((X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X3)) := superpose eq9 eq20
  have eq49 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = X0 := superpose eq20 eq33
  have eq52 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ (X3 ◇ X4))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X3 := superpose eq49 eq11
  have eq58 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq52 eq16
  have eq64 (X0 X2 : G) : X0 = X2 := superpose eq7 eq58
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq95 eq64


@[equational_result]
theorem Equation25095_implies_Equation2 (G : Type*) [Magma G] (h : Equation25095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X3))) = X2 := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X3)))) ◇ X0) = X2 := superpose eq10 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X3))) = X2 := superpose eq10 eq7
  have eq43 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq10 eq16
  have eq68 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq10 eq9
  have eq97 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X2)) = X1 := superpose eq10 eq43
  have eq100 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq43 eq43
  have eq128 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1)) = X0 := superpose eq68 eq10
  have eq269 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq43 eq100
  have eq294 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X3))) ◇ X0) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X3)))) = X2 := superpose eq100 eq17
  have eq368 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X2))) = X1 := superpose eq269 eq13
  have eq371 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) = X0 := superpose eq269 eq128
  have eq401 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq269 eq371
  have eq402 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq43 eq401
  have eq404 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X2))) = X1 := superpose eq402 eq368
  have eq409 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq97 eq404
  have eq412 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X3)))) = X2 := superpose eq409 eq294
  have eq721 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X3))) = X2 := superpose eq409 eq412
  have eq722 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X3)) = X2 := superpose eq409 eq721
  have eq723 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X2 := superpose eq409 eq722
  have eq724 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq409 eq723
  have eq725 (X0 X3 : G) : X0 = X3 := superpose eq724 eq724
  have eq730 (X0 : G) : sK0 ≠ X0 := superpose eq725 eq8
  subsumption eq730 eq725


@[equational_result]
theorem Equation25096_implies_Equation2 (G : Type*) [Magma G] (h : Equation25096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X4)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq109 eq39


@[equational_result]
theorem Equation25099_implies_Equation2 (G : Type*) [Magma G] (h : Equation25099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X3))) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((X2 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2))) = (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq7 eq12
  have eq49 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := superpose eq7 eq16
  have eq123 (X0 X3 : G) : X0 = X3 := superpose eq49 eq49
  have eq236 (X0 : G) : sK0 ≠ X0 := superpose eq123 eq8
  subsumption eq236 eq123


@[equational_result]
theorem Equation25100_implies_Equation2 (G : Type*) [Magma G] (h : Equation25100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation25102_implies_Equation2 (G : Type*) [Magma G] (h : Equation25102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq12
  have eq72 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq164 eq72


@[equational_result]
theorem Equation25103_implies_Equation2 (G : Type*) [Magma G] (h : Equation25103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation25104_implies_Equation2 (G : Type*) [Magma G] (h : Equation25104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq11 eq11
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq164 eq60


@[equational_result]
theorem Equation25105_implies_Equation2 (G : Type*) [Magma G] (h : Equation25105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation25108_implies_Equation2 (G : Type*) [Magma G] (h : Equation25108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq7 eq11
  have eq17 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq11 eq7
  have eq21 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq17 eq13
  have eq45 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq21 eq11
  have eq47 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq45 eq21
  have eq50 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq45 eq47
  have eq52 (X0 X1 : G) : X0 = X1 := superpose eq50 eq45
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq54 eq52


@[equational_result]
theorem Equation25111_implies_Equation2 (G : Type*) [Magma G] (h : Equation25111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq125 eq59


@[equational_result]
theorem Equation25113_implies_Equation2 (G : Type*) [Magma G] (h : Equation25113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X4) = X3 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X3 ◇ X0)) ◇ X4) = X3 := superpose eq10 eq10
  have eq23 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq11 eq14
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq140 eq52


@[equational_result]
theorem Equation25115_implies_Equation2 (G : Type*) [Magma G] (h : Equation25115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation25118_implies_Equation2 (G : Type*) [Magma G] (h : Equation25118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq18 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq15 eq14
  have eq26 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq15 eq18
  have eq27 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq26 eq19
  have eq37 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq27 eq11
  have eq40 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq37 eq27
  have eq42 (X0 X1 : G) : X0 = X1 := superpose eq40 eq37
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq55 eq42


@[equational_result]
theorem Equation25121_implies_Equation2 (G : Type*) [Magma G] (h : Equation25121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq61 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq126 eq61


@[equational_result]
theorem Equation25123_implies_Equation2 (G : Type*) [Magma G] (h : Equation25123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) ◇ X0) = X3 := superpose eq7 eq7
  have eq30 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X0))) ◇ X4) = X3 := superpose eq7 eq10
  have eq35 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0)) ◇ X4) = X3 := superpose eq10 eq10
  have eq57 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq30 eq35
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq7 eq57
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq132 eq58


@[equational_result]
theorem Equation25124_implies_Equation2 (G : Type*) [Magma G] (h : Equation25124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X2))) = ((X1 ◇ X0) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq9
  have eq26 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) = X1 := superpose eq9 eq7
  have eq31 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X3 := superpose eq9 eq7
  have eq37 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq31 eq10
  have eq39 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3)) = X1 := superpose eq37 eq26
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq37 eq22
  have eq52 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X3 ◇ X3)) = X1 := superpose eq37 eq39
  have eq53 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq37 eq40
  have eq54 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X1 := superpose eq53 eq52
  have eq59 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq53 eq54
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq59 eq59
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq65 eq60


@[equational_result]
theorem Equation25125_implies_Equation2 (G : Type*) [Magma G] (h : Equation25125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq9
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation25127_implies_Equation2 (G : Type*) [Magma G] (h : Equation25127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X3))) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X1 ◇ X1))) := superpose eq10 eq10
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := superpose eq7 eq9
  have eq39 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq22 eq22
  have eq40 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq22 eq22
  have eq43 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X2 := superpose eq22 eq9
  have eq52 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq22 eq10
  have eq55 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq40 eq39
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X1))) := superpose eq55 eq15
  have eq73 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1)) := superpose eq55 eq57
  have eq74 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1)) := superpose eq55 eq73
  have eq87 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq55 eq52
  have eq90 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3))) ◇ X1) := superpose eq22 eq11
  have eq94 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0) := superpose eq22 eq11
  have eq95 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = ((((((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (((X1 ◇ X2) ◇ X0) ◇ X4))) ◇ X1) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) ◇ (((((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (((X1 ◇ X2) ◇ X0) ◇ X4))) ◇ X1) ◇ X5))) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (((X1 ◇ X2) ◇ X0) ◇ X4)))) := superpose eq11 eq11
  have eq115 (X0 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = X0 := superpose eq55 eq94
  have eq199 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq43 eq43
  have eq238 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq55 eq74
  have eq250 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X1 := superpose eq74 eq43
  have eq280 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq115 eq74
  have eq304 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq55 eq280
  have eq407 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq304 eq43
  have eq547 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq7 eq407
  have eq585 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq250 eq547
  have eq586 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (((X1 ◇ X2) ◇ X0) ◇ X4)))) := superpose eq585 eq95
  have eq590 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq585 eq90
  have eq725 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) := superpose eq585 eq586
  have eq726 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq585 eq725
  have eq727 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq726 eq238
  have eq732 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq590 eq87
  have eq734 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq585 eq732
  have eq735 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq734 eq727
  have eq739 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq734 eq199
  have eq751 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq735 eq304
  have eq758 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq751 eq735
  have eq770 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq758 eq739
  have eq771 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq758 eq770
  have eq937 (X0 X2 : G) : X0 = X2 := superpose eq771 eq771
  have eq945 (X0 : G) : sK0 ≠ X0 := superpose eq937 eq8
  subsumption eq945 eq937


@[equational_result]
theorem Equation25129_implies_Equation2 (G : Type*) [Magma G] (h : Equation25129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ (X3 ◇ X5)) = X3 := superpose eq7 eq7
  have eq11 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq7 eq11
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X0 := superpose eq11 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq17 eq13
  have eq25 (X0 X3 X5 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X5)) = X3 := superpose eq21 eq9
  have eq32 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq11 eq25
  have eq34 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq25 eq11
  have eq35 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq32 eq34
  have eq45 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq35 eq11
  have eq48 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq45 eq21
  have eq52 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq45 eq48
  have eq53 (X0 X1 : G) : X0 = X1 := superpose eq52 eq45
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq55 eq53


@[equational_result]
theorem Equation25131_implies_Equation2 (G : Type*) [Magma G] (h : Equation25131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq10 eq7
  have eq56 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X5))) = X2 := superpose eq18 eq18
  have eq58 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X3))) := superpose eq10 eq18
  have eq90 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq56 eq58
  have eq91 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq90 eq26
  have eq122 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0) = X2 := superpose eq90 eq91
  have eq123 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = X2 := superpose eq90 eq122
  have eq124 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq90 eq123
  have eq225 (X0 X2 : G) : X0 = X2 := superpose eq124 eq124
  have eq227 (X0 : G) : sK0 ≠ X0 := superpose eq225 eq8
  subsumption eq227 eq225


@[equational_result]
theorem Equation25132_implies_Equation2 (G : Type*) [Magma G] (h : Equation25132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ X0) = X3 := superpose eq7 eq7
  have eq30 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq30 eq30
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq84 eq39


@[equational_result]
theorem Equation25133_implies_Equation2 (G : Type*) [Magma G] (h : Equation25133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq154 eq67


@[equational_result]
theorem Equation25135_implies_Equation2 (G : Type*) [Magma G] (h : Equation25135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ X2)) := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) = (((X2 ◇ X1) ◇ X3) ◇ X0) := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) = (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq10
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) = X1 := superpose eq10 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq10 eq7
  have eq30 (X0 X1 X2 X3 : G) : ((((X2 ◇ X1) ◇ X3) ◇ X0) ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = X3 := superpose eq18 eq9
  have eq79 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) = X1 := superpose eq10 eq21
  have eq109 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))))) = X3 := superpose eq10 eq30
  have eq110 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ (X0 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ (X4 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1))))) = X3 := superpose eq21 eq30
  have eq140 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X4) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)))) = X3 := superpose eq10 eq109
  have eq141 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ (X0 ◇ ((X1 ◇ X4) ◇ (((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1)))) = X3 := superpose eq10 eq110
  have eq163 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq22 eq22
  have eq174 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))))) := superpose eq22 eq30
  have eq212 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) ◇ (X2 ◇ X0)) := superpose eq10 eq12
  have eq234 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) := superpose eq12 eq21
  have eq286 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))))) := superpose eq10 eq79
  have eq300 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0))) ◇ (X1 ◇ X2))) := superpose eq79 eq10
  have eq320 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))))) := superpose eq20 eq286
  have eq347 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq10 eq23
  have eq382 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X2))) ◇ (X3 ◇ X0)) = ((((X0 ◇ X2) ◇ X1) ◇ X3) ◇ X0) := superpose eq23 eq10
  have eq413 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((((X2 ◇ X0) ◇ X2) ◇ X1) ◇ X2)) := superpose eq382 eq300
  have eq421 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := superpose eq7 eq163
  have eq432 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq30 eq163
  have eq472 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq432 eq421
  have eq534 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) := superpose eq472 eq174
  have eq558 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq534 eq320
  have eq572 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X2 ◇ X0)) := superpose eq558 eq212
  have eq574 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq558 eq234
  have eq609 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose eq574 eq79
  have eq621 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq574 eq534
  have eq623 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq558 eq609
  have eq635 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ (X2 ◇ X0)) := superpose eq621 eq572
  have eq639 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ X2)) := superpose eq635 eq472
  have eq697 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq639 eq13
  have eq779 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) = X2 := superpose eq623 eq697
  have eq780 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq779 eq347
  have eq782 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq780 eq163
  have eq786 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X1 ◇ ((X2 ◇ X1) ◇ X2)) := superpose eq782 eq413
  have eq807 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq782 eq786
  have eq809 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))) = X3 := superpose eq807 eq140
  have eq811 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ (X0 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1))) = X3 := superpose eq807 eq141
  have eq878 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) = X3 := superpose eq807 eq809
  have eq879 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ ((X2 ◇ X0) ◇ X2)) = X3 := superpose eq807 eq878
  have eq880 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ X2) = X3 := superpose eq782 eq879
  have eq881 (X0 X2 X3 X4 : G) : ((((X2 ◇ X0) ◇ X3) ◇ X4) ◇ X2) = X3 := superpose eq807 eq880
  have eq885 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ (((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X1)) = X3 := superpose eq807 eq811
  have eq886 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) = X3 := superpose eq807 eq885
  have eq887 (X0 X1 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ X1) = X3 := superpose eq782 eq886
  have eq889 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq887 eq881
  have eq890 (X0 X3 : G) : X0 = X3 := superpose eq889 eq889
  have eq892 (X0 : G) : sK0 ≠ X0 := superpose eq890 eq8
  subsumption eq892 eq890


@[equational_result]
theorem Equation25136_implies_Equation2 (G : Type*) [Magma G] (h : Equation25136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = ((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) ◇ (X4 ◇ X3)) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) = X4 := superpose eq10 eq9
  have eq40 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq9
  have eq51 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq40 eq7
  have eq78 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq18 eq7
  have eq84 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq51 eq9
  have eq85 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq51 eq7
  have eq92 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq51 eq84
  have eq94 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) ◇ (X4 ◇ X3)) ◇ X2) = X4 := superpose eq92 eq28
  have eq103 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq51 eq85
  have eq106 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) = (((X2 ◇ X2) ◇ X3) ◇ X2) := superpose eq103 eq12
  have eq114 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq103 eq40
  have eq135 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X1)) = X2 := superpose eq114 eq78
  have eq144 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ X1) := superpose eq114 eq10
  have eq165 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) = ((X2 ◇ X3) ◇ X2) := superpose eq114 eq106
  have eq174 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X2 := superpose eq114 eq135
  have eq194 (X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X2) ◇ (X4 ◇ X3)) ◇ X2) = X4 := superpose eq165 eq94
  have eq195 (X2 X4 : G) : (X4 ◇ X2) = X4 := superpose eq174 eq194
  have eq196 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X1))) = (X1 ◇ X0) := superpose eq195 eq144
  have eq229 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := superpose eq195 eq196
  have eq230 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq195 eq229
  have eq231 (X0 X3 : G) : X0 = X3 := superpose eq230 eq230
  have eq233 (X0 : G) : sK0 ≠ X0 := superpose eq231 eq8
  subsumption eq233 eq231


@[equational_result]
theorem Equation25137_implies_Equation2 (G : Type*) [Magma G] (h : Equation25137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation25139_implies_Equation2 (G : Type*) [Magma G] (h : Equation25139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4))) ◇ X0) = X3 := superpose eq7 eq7
  have eq36 (X0 X4 X5 X6 : G) : ((X0 ◇ (X4 ◇ (X0 ◇ X5))) ◇ X6) = X4 := superpose eq7 eq11
  have eq40 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ X5) = X3 := superpose eq7 eq11
  have eq63 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq36 eq40
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq7 eq63
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq170 eq64


@[equational_result]
theorem Equation25140_implies_Equation2 (G : Type*) [Magma G] (h : Equation25140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ (X5 ◇ (X4 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X4)))) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X6 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X6) = X2 := superpose eq7 eq11
  have eq23 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X5 ◇ (X4 ◇ X2))) = X3 := superpose eq12 eq9
  have eq33 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq57 eq33


@[equational_result]
theorem Equation25141_implies_Equation2 (G : Type*) [Magma G] (h : Equation25141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ (X5 ◇ X5)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X3))) = ((X1 ◇ X0) ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X1) ◇ X4) = ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X5 ◇ X5)) := superpose eq10 eq7
  have eq38 (X1 X3 X4 : G) : ((X3 ◇ X1) ◇ X4) = X1 := superpose eq7 eq34
  have eq39 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ X5)) = X3 := superpose eq38 eq9
  have eq62 (X0 X4 : G) : X0 = X4 := superpose eq7 eq39
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq75 eq62


@[equational_result]
theorem Equation25142_implies_Equation2 (G : Type*) [Magma G] (h : Equation25142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X6 X7 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ (X6 ◇ X7)) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X3 := superpose eq7 eq9
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation25144_implies_Equation2 (G : Type*) [Magma G] (h : Equation25144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))))) ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq9 eq9
  have eq22 (X0 X3 : G) : ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3)) = X0 := superpose eq10 eq9
  have eq32 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq22 eq22
  have eq39 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq22 eq7
  have eq77 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq32 eq7
  have eq83 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq32 eq22
  have eq85 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq83
  have eq91 (X0 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq85 eq22
  have eq95 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq85 eq39
  have eq101 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq85 eq77
  have eq106 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq85 eq101
  have eq107 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq85 eq106
  have eq148 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq85 eq7
  have eq213 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq7 eq95
  have eq215 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq9 eq95
  have eq254 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))))) ◇ (X0 ◇ X1)) := superpose eq18 eq11
  have eq284 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq107 eq18
  have eq310 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq7 eq284
  have eq311 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq107 eq310
  have eq313 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq311 eq148
  have eq318 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq313 eq213
  have eq321 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq313 eq318
  have eq353 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1))))) ◇ (X0 ◇ X1)) := superpose eq321 eq254
  have eq447 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq321 eq353
  have eq448 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq321 eq447
  have eq449 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq321 eq448
  have eq450 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq85 eq449
  have eq452 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq450 eq215
  have eq453 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq450 eq452
  have eq592 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq321 eq91
  have eq594 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq321 eq592
  have eq595 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq594 eq453
  have eq599 (X0 X1 : G) : X0 = X1 := superpose eq595 eq594
  have eq601 (X0 : G) : sK0 ≠ X0 := superpose eq599 eq8
  subsumption eq601 eq599


@[equational_result]
theorem Equation25145_implies_Equation2 (G : Type*) [Magma G] (h : Equation25145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq10
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq7
  have eq18 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq13 eq14
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq10 eq9
  have eq33 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq9 eq10
  have eq39 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq32 eq33
  have eq70 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq10 eq18
  have eq74 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq10 eq70
  have eq75 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq74 eq39
  have eq82 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq74 eq75
  have eq86 (X0 X1 : G) : X0 = X1 := superpose eq82 eq74
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq88 eq86


@[equational_result]
theorem Equation25146_implies_Equation2 (G : Type*) [Magma G] (h : Equation25146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq7
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq11 eq9
  have eq32 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq9 eq11
  have eq34 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq31 eq32
  have eq45 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq11 eq15
  have eq49 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq15 eq11
  have eq51 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq45 eq49
  have eq52 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ X1) := superpose eq51 eq34
  have eq60 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq51 eq52
  have eq63 (X0 X1 : G) : X0 = X1 := superpose eq60 eq51
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq65 eq63


@[equational_result]
theorem Equation25148_implies_Equation2 (G : Type*) [Magma G] (h : Equation25148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq9 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq7 eq9
  have eq21 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq11 eq14
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq21 eq15
  have eq44 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq22
  have eq96 (X0 X2 : G) : X0 = X2 := superpose eq7 eq44
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq158 eq96


@[equational_result]
theorem Equation25150_implies_Equation2 (G : Type*) [Magma G] (h : Equation25150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X4)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq160 eq59


@[equational_result]
theorem Equation25153_implies_Equation2 (G : Type*) [Magma G] (h : Equation25153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((X3 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X1) = (X0 ◇ ((X3 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X3 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq7 eq9
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq96 eq32


@[equational_result]
theorem Equation25154_implies_Equation2 (G : Type*) [Magma G] (h : Equation25154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation25156_implies_Equation2 (G : Type*) [Magma G] (h : Equation25156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq11
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq118 eq41


@[equational_result]
theorem Equation25157_implies_Equation2 (G : Type*) [Magma G] (h : Equation25157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation25158_implies_Equation2 (G : Type*) [Magma G] (h : Equation25158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq11 eq11
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq135 eq38


@[equational_result]
theorem Equation25159_implies_Equation2 (G : Type*) [Magma G] (h : Equation25159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation25161_implies_Equation2 (G : Type*) [Magma G] (h : Equation25161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X1 ◇ (X0 ◇ (X3 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1))))) = X0 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) = X0 := superpose eq9 eq9
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq10
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X0)) := superpose eq10 eq10
  have eq52 (X0 X3 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)) = X3 := superpose eq14 eq9
  have eq63 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ (X0 ◇ X1)) := superpose eq10 eq11
  have eq69 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1))))))) = ((X0 ◇ (((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1))))))) ◇ (X4 ◇ X0))) ◇ X0) := superpose eq14 eq11
  have eq87 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq7 eq52
  have eq88 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq52 eq52
  have eq97 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq52 eq10
  have eq98 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) := superpose eq52 eq9
  have eq109 (X0 X1 X2 X4 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1))))) ◇ X0) ◇ X0) = ((X0 ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1))))) ◇ X0) ◇ X0) ◇ (X4 ◇ X0))) ◇ X0) := superpose eq87 eq69
  have eq112 (X0 X4 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X4 ◇ X0))) ◇ X0) := superpose eq14 eq109
  have eq128 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq15
  have eq154 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq128 eq14
  have eq162 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq128 eq9
  have eq164 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq128 eq10
  have eq171 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq128 eq154
  have eq173 (X0 X4 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X4 ◇ X0))) ◇ X0) := superpose eq171 eq112
  have eq179 (X0 X4 : G) : ((X0 ◇ (X0 ◇ (X4 ◇ X0))) ◇ X0) = X0 := superpose eq171 eq173
  have eq192 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq171 eq162
  have eq193 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq171 eq164
  have eq194 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq179 eq193
  have eq195 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq171 eq194
  have eq197 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq195 eq97
  have eq336 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X0) := superpose eq52 eq17
  have eq366 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2)))) := superpose eq17 eq52
  have eq393 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq195 eq9
  have eq426 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq171 eq393
  have eq454 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) := superpose eq52 eq29
  have eq507 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = X1 := superpose eq195 eq454
  have eq508 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq171 eq507
  have eq509 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq508 eq31
  have eq512 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq508 eq509
  have eq514 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ (X0 ◇ X1)) = X0 := superpose eq512 eq63
  have eq517 (X0 X1 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq87 eq514
  have eq518 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq426 eq517
  have eq523 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq518 eq192
  have eq524 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2)))) = X0 := superpose eq523 eq366
  have eq526 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq523 eq88
  have eq531 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq524 eq336
  have eq557 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq531 eq98
  have eq617 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq526 eq557
  have eq646 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq526 eq617
  have eq647 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq646 eq197
  have eq650 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = (X0 ◇ ((X1 ◇ (X0 ◇ (X3 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq646 eq12
  have eq718 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq171 eq647
  have eq719 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X0 := superpose eq718 eq650
  have eq720 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq646 eq719
  have eq721 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq646 eq720
  have eq728 (X0 X2 : G) : X0 = X2 := superpose eq721 eq721
  have eq733 (X0 : G) : sK0 ≠ X0 := superpose eq728 eq8
  subsumption eq733 eq728


@[equational_result]
theorem Equation25163_implies_Equation2 (G : Type*) [Magma G] (h : Equation25163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq17 eq13
  have eq45 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq11 eq15
  have eq49 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq15 eq11
  have eq51 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq45 eq49
  have eq56 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq51 eq19
  have eq61 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq51 eq56
  have eq64 (X0 X2 : G) : X0 = X2 := superpose eq61 eq61
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq72 eq64


@[equational_result]
theorem Equation25165_implies_Equation2 (G : Type*) [Magma G] (h : Equation25165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))))) = (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1))))) := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq10 eq9
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq9 eq29
  have eq47 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) := superpose eq46 eq14
  have eq63 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))))) = X0 := superpose eq46 eq47
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1)) = X0 := superpose eq46 eq63
  have eq65 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1) = X0 := superpose eq46 eq64
  have eq66 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq46 eq65
  have eq133 (X0 X1 : G) : X0 = X1 := superpose eq46 eq66
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq133 eq8
  subsumption eq138 eq133


@[equational_result]
theorem Equation25167_implies_Equation2 (G : Type*) [Magma G] (h : Equation25167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X4)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq146 eq45


@[equational_result]
theorem Equation25169_implies_Equation2 (G : Type*) [Magma G] (h : Equation25169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq10
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq85 eq34


@[equational_result]
theorem Equation25171_implies_Equation2 (G : Type*) [Magma G] (h : Equation25171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation25173_implies_Equation2 (G : Type*) [Magma G] (h : Equation25173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X5 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = ((X1 ◇ X0) ◇ (X4 ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X4 X5 X6 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ (X6 ◇ X0)) = X4 := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq7 eq9
  have eq27 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ (X4 ◇ X1)) := superpose eq7 eq10
  have eq60 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq16 eq27
  have eq61 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq60 eq18
  have eq71 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq60 eq61
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq71 eq71
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq77 eq72


@[equational_result]
theorem Equation25174_implies_Equation2 (G : Type*) [Magma G] (h : Equation25174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq11 eq11
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq170 eq65


@[equational_result]
theorem Equation25175_implies_Equation2 (G : Type*) [Magma G] (h : Equation25175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X5 ◇ X5)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X1 := superpose eq9 eq9
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq174 eq64


@[equational_result]
theorem Equation25176_implies_Equation2 (G : Type*) [Magma G] (h : Equation25176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation25179_implies_Equation2 (G : Type*) [Magma G] (h : Equation25179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq10 eq9
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq10
  have eq15 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq7
  have eq23 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq14 eq15
  have eq25 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq23 eq12
  have eq28 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq23 eq25
  have eq29 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq28 eq10
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq28 eq29
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq42 eq32


@[equational_result]
theorem Equation25180_implies_Equation2 (G : Type*) [Magma G] (h : Equation25180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq14 eq13
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq14 eq17
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq23 eq18
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq24
  have eq39 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq31 eq24
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq14 eq39
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq48 eq40


@[equational_result]
theorem Equation25182_implies_Equation2 (G : Type*) [Magma G] (h : Equation25182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X3))) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq43 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := superpose eq7 eq10
  have eq48 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) = X3 := superpose eq10 eq7
  have eq70 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = X3 := superpose eq43 eq48
  have eq77 (X0 X3 : G) : X0 = X3 := superpose eq7 eq70
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq161 eq77


@[equational_result]
theorem Equation25183_implies_Equation2 (G : Type*) [Magma G] (h : Equation25183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X2))) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) ◇ X2)) = X1 := superpose eq9 eq10
  have eq44 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (((X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ X3) ◇ ((X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ X3)))) ◇ X0) = X2 := superpose eq12 eq7
  have eq52 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3))))) ◇ X0) = X2 := superpose eq9 eq44
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq52 eq12
  have eq64 (X0 X2 : G) : X0 = X2 := superpose eq54 eq54
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq125 eq64


@[equational_result]
theorem Equation25184_implies_Equation2 (G : Type*) [Magma G] (h : Equation25184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X4)) = X1 := superpose eq7 eq7
  have eq31 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq140 eq40


@[equational_result]
theorem Equation25187_implies_Equation2 (G : Type*) [Magma G] (h : Equation25187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq10 eq12
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25188_implies_Equation2 (G : Type*) [Magma G] (h : Equation25188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation25190_implies_Equation2 (G : Type*) [Magma G] (h : Equation25190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) ◇ X0) = X3 := superpose eq7 eq7
  have eq32 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq12
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq32
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq147 eq42


@[equational_result]
theorem Equation25191_implies_Equation2 (G : Type*) [Magma G] (h : Equation25191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation25192_implies_Equation2 (G : Type*) [Magma G] (h : Equation25192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X3 ◇ X3) = (X0 ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation25193_implies_Equation2 (G : Type*) [Magma G] (h : Equation25193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation25195_implies_Equation2 (G : Type*) [Magma G] (h : Equation25195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X4))) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))))) = X0 := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X0))) := superpose eq9 eq11
  have eq32 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq11
  have eq38 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq49 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq32 eq9
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq97 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X0) := superpose eq7 eq38
  have eq102 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq32 eq38
  have eq119 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq38 eq32
  have eq120 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq119 eq102
  have eq122 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq120 eq119
  have eq125 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq122 eq49
  have eq202 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq122 eq9
  have eq389 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq125 eq38
  have eq412 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq125 eq389
  have eq417 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq412 eq202
  have eq420 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X0 ◇ X0) := superpose eq417 eq74
  have eq431 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq122 eq420
  have eq433 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X1 ◇ X0) := superpose eq431 eq97
  have eq496 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq431 eq433
  have eq498 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq496 eq30
  have eq517 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq496 eq498
  have eq518 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq496 eq517
  have eq519 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq496 eq518
  have eq520 (X0 X1 : G) : X0 = X1 := superpose eq122 eq519
  have eq525 (X0 : G) : sK0 ≠ X0 := superpose eq520 eq8
  subsumption eq525 eq520


@[equational_result]
theorem Equation25196_implies_Equation2 (G : Type*) [Magma G] (h : Equation25196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X5))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) := superpose eq7 eq11
  have eq22 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X7 ◇ ((X0 ◇ (X4 ◇ (X3 ◇ (X5 ◇ X6)))) ◇ (X8 ◇ X9))))) := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X2) ◇ (X4 ◇ X5))))) = X0 := superpose eq11 eq9
  have eq38 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq11 eq9
  have eq44 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq38 eq13
  have eq45 (X0 X1 X2 X3 X7 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ X7) := superpose eq44 eq22
  have eq55 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq44 eq23
  have eq57 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq55 eq45
  have eq61 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq57 eq44
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq11 eq61
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq75 eq65


@[equational_result]
theorem Equation25197_implies_Equation2 (G : Type*) [Magma G] (h : Equation25197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq30 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq11 eq9
  have eq37 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq14 eq30
  have eq45 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq14 eq9
  have eq82 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := superpose eq7 eq37
  have eq101 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq11 eq82
  have eq102 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq101 eq45
  have eq138 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq101 eq102
  have eq139 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq101 eq138
  have eq166 (X0 X1 : G) : X0 = X1 := superpose eq101 eq139
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq166 eq8
  subsumption eq172 eq166


@[equational_result]
theorem Equation25198_implies_Equation2 (G : Type*) [Magma G] (h : Equation25198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X7 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X7)) = X2 := superpose eq7 eq7
  have eq11 (X0 X6 : G) : (X0 ◇ (X0 ◇ X6)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) := superpose eq7 eq11
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq17 eq13
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq11 eq9
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq9 eq11
  have eq32 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq29 eq31
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq32 eq19
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq11 eq36
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq50 eq40


@[equational_result]
theorem Equation25200_implies_Equation2 (G : Type*) [Magma G] (h : Equation25200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X4))) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = X1 := superpose eq7 eq9
  have eq44 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4))) = X0 := superpose eq9 eq10
  have eq69 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X1) := superpose eq44 eq11
  have eq70 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X0 := superpose eq7 eq69
  have eq112 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq70 eq15
  have eq130 (X0 X2 : G) : X0 = X2 := superpose eq9 eq112
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq130 eq8
  subsumption eq161 eq130


@[equational_result]
theorem Equation25201_implies_Equation2 (G : Type*) [Magma G] (h : Equation25201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X4))) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) = (X0 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X6))) ◇ X1)) := superpose eq7 eq10
  have eq32 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) = X2 := superpose eq10 eq7
  have eq45 (X0 X1 X2 X3 X7 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X7))) ◇ X3)) = X2 := superpose eq11 eq11
  have eq70 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) = X2 := superpose eq45 eq22
  have eq72 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X2 := superpose eq70 eq32
  have eq80 (X0 X4 : G) : X0 = X4 := superpose eq7 eq72
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq182 eq80


@[equational_result]
theorem Equation25202_implies_Equation2 (G : Type*) [Magma G] (h : Equation25202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X4))) = ((X1 ◇ X0) ◇ (X1 ◇ X4)) := superpose eq7 eq7
  have eq33 (X0 X1 X4 X5 : G) : ((X5 ◇ X1) ◇ (X5 ◇ X4)) = X0 := superpose eq7 eq10
  have eq85 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq173 eq85


@[equational_result]
theorem Equation25203_implies_Equation2 (G : Type*) [Magma G] (h : Equation25203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X6 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X6)) = X1 := superpose eq7 eq7
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq32
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq143 eq42


@[equational_result]
theorem Equation25205_implies_Equation2 (G : Type*) [Magma G] (h : Equation25205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X4))) = ((X1 ◇ X0) ◇ (X3 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X4))) ◇ X5))) ◇ X0) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ (X4 ◇ X5))) ◇ X6))) = (((X4 ◇ X3) ◇ X2) ◇ X0) := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4))) = X0 := superpose eq7 eq10
  have eq41 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X0) = X3 := superpose eq25 eq12
  have eq53 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq41 eq41
  have eq68 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X4)) = X0 := superpose eq53 eq28
  have eq98 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq53 eq68
  have eq99 (X0 X3 : G) : X0 = X3 := superpose eq98 eq98
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq104 eq99


@[equational_result]
theorem Equation25206_implies_Equation2 (G : Type*) [Magma G] (h : Equation25206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X2 ◇ X2)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq72 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq169 eq72


@[equational_result]
theorem Equation25207_implies_Equation2 (G : Type*) [Magma G] (h : Equation25207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq41 eq15


@[equational_result]
theorem Equation25208_implies_Equation2 (G : Type*) [Magma G] (h : Equation25208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 X6 : G) : (X0 ◇ (X4 ◇ X6)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation25210_implies_Equation2 (G : Type*) [Magma G] (h : Equation25210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X5 ◇ X3) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X3 ◇ X4))) = ((X1 ◇ X0) ◇ (X2 ◇ X1)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ X4) ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X5)) = X0 := superpose eq7 eq10
  have eq69 (X0 X4 X5 : G) : ((X5 ◇ X4) ◇ X0) = X0 := superpose eq19 eq33
  have eq86 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq7 eq69
  have eq104 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X1)) = X0 := superpose eq86 eq7
  have eq124 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X0 := superpose eq86 eq104
  have eq125 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X1) = X0 := superpose eq86 eq124
  have eq126 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq86 eq125
  have eq127 (X0 X3 : G) : X0 = X3 := superpose eq126 eq126
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq127 eq8
  subsumption eq129 eq127


@[equational_result]
theorem Equation25211_implies_Equation2 (G : Type*) [Magma G] (h : Equation25211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X2)) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation25212_implies_Equation2 (G : Type*) [Magma G] (h : Equation25212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X3 ◇ X4) = (X0 ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq155 eq49


@[equational_result]
theorem Equation25213_implies_Equation2 (G : Type*) [Magma G] (h : Equation25213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation25215_implies_Equation2 (G : Type*) [Magma G] (h : Equation25215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0) = X3 := superpose eq7 eq7
  have eq32 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq12
  have eq42 (X0 X5 : G) : X0 = X5 := superpose eq7 eq32
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq147 eq42


@[equational_result]
theorem Equation25216_implies_Equation2 (G : Type*) [Magma G] (h : Equation25216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 X6 : G) : (X0 ◇ (X6 ◇ X2)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation25217_implies_Equation2 (G : Type*) [Magma G] (h : Equation25217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X6 ◇ X4)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation25218_implies_Equation2 (G : Type*) [Magma G] (h : Equation25218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X4 ◇ X5) = (X0 ◇ (X6 ◇ X6)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation25219_implies_Equation2 (G : Type*) [Magma G] (h : Equation25219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X4 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation25222_implies_Equation2 (G : Type*) [Magma G] (h : Equation25222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X0))) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))))) ◇ X0) := superpose eq7 eq7
  have eq24 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq9
  have eq33 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq9 eq24
  have eq41 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq24 eq7
  have eq42 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X2 ◇ (X2 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X3)) := superpose eq24 eq9
  have eq71 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) = ((X3 ◇ (X3 ◇ (((X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ ((X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))))) ◇ X1) := superpose eq11 eq11
  have eq91 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq41
  have eq105 (X0 X1 X2 : G) : (((X2 ◇ (X2 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X1 := superpose eq24 eq41
  have eq116 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq10 eq91
  have eq171 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ X0) := superpose eq7 eq116
  have eq183 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X3)) := superpose eq116 eq9
  have eq189 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq171 eq7
  have eq191 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0)))) ◇ X0) := superpose eq171 eq11
  have eq220 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq171 eq24
  have eq226 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq171 eq33
  have eq238 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) = ((X3 ◇ (X3 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))))) ◇ X1) := superpose eq171 eq71
  have eq240 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq171 eq191
  have eq243 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq240 eq42
  have eq246 (X0 X1 X2 : G) : (((X2 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq240 eq105
  have eq252 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq240 eq246
  have eq274 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq220 eq226
  have eq275 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq252 eq274
  have eq276 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose eq252 eq275
  have eq277 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq171 eq276
  have eq284 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) = ((X3 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) ◇ X1) := superpose eq171 eq238
  have eq285 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = ((X3 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) := superpose eq171 eq284
  have eq293 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3)) := superpose eq171 eq183
  have eq294 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) = X2 := superpose eq252 eq293
  have eq300 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq189 eq277
  have eq301 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq277 eq116
  have eq305 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq300 eq301
  have eq306 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq305 eq171
  have eq314 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq305 eq285
  have eq318 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq306 eq243
  have eq319 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq306 eq294
  have eq326 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X0 := superpose eq319 eq314
  have eq327 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq326 eq318
  have eq330 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq327 eq189
  have eq340 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq327 eq330
  have eq345 (X0 X1 : G) : X0 = X1 := superpose eq340 eq327
  have eq347 (X0 : G) : sK0 ≠ X0 := superpose eq345 eq8
  subsumption eq347 eq345


@[equational_result]
theorem Equation25225_implies_Equation2 (G : Type*) [Magma G] (h : Equation25225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3)))) = (((X2 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X4)) := superpose eq7 eq9
  have eq35 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3)))) = X2 := superpose eq10 eq18
  have eq39 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ X2)) = X0 := superpose eq7 eq10
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq35 eq39
  have eq60 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq59 eq35
  have eq68 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq60 eq11
  have eq71 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = X1 := superpose eq60 eq10
  have eq80 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X1 := superpose eq68 eq71
  have eq81 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq68 eq80
  have eq96 (X0 X2 : G) : X0 = X2 := superpose eq81 eq81
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq104 eq96


@[equational_result]
theorem Equation25227_implies_Equation2 (G : Type*) [Magma G] (h : Equation25227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X0 ◇ (X0 ◇ (X3 ◇ X3))) ◇ X4) = X3 := superpose eq7 eq11
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := superpose eq12 eq9
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq11 eq23
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq40 eq34


@[equational_result]
theorem Equation25228_implies_Equation2 (G : Type*) [Magma G] (h : Equation25228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X3 ◇ X3)) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq9 eq9
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq26 eq18


@[equational_result]
theorem Equation25229_implies_Equation2 (G : Type*) [Magma G] (h : Equation25229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation25232_implies_Equation2 (G : Type*) [Magma G] (h : Equation25232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X2))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X2))) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X2))) = (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1))) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0) := superpose eq7 eq10
  have eq27 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) := superpose eq7 eq11
  have eq147 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = ((((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) ◇ (X0 ◇ X2)) := superpose eq7 eq27
  have eq158 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) = X3 := superpose eq27 eq7
  have eq200 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := superpose eq10 eq147
  have eq201 (X0 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X2))) = (X2 ◇ X0) := superpose eq200 eq11
  have eq202 (X0 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X2))) = ((X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0) := superpose eq200 eq16
  have eq226 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq201 eq9
  have eq284 (X0 X2 : G) : (X2 ◇ X0) = ((X2 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq201 eq202
  have eq313 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X3 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X0)) = X3 := superpose eq284 eq158
  have eq314 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X0)) = X3 := superpose eq201 eq313
  have eq317 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq314 eq226
  have eq335 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq317 eq200
  have eq337 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq335 eq201
  have eq342 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq337 eq314
  have eq347 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X3 := superpose eq337 eq342
  have eq348 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq337 eq347
  have eq349 (X0 X3 : G) : X0 = X3 := superpose eq348 eq348
  have eq354 (X0 : G) : sK0 ≠ X0 := superpose eq349 eq8
  subsumption eq354 eq349


@[equational_result]
theorem Equation25235_implies_Equation2 (G : Type*) [Magma G] (h : Equation25235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2)) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) = (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X3)) := superpose eq10 eq9
  have eq39 (X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) = X1 := superpose eq10 eq21
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq39 eq12
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq40 eq22
  have eq42 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq39 eq41
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) = X1 := superpose eq42 eq10
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq43 eq11
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq7 eq50
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq104 eq51


@[equational_result]
theorem Equation25237_implies_Equation2 (G : Type*) [Magma G] (h : Equation25237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X0) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4) = X3 := superpose eq7 eq10
  have eq15 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) ◇ X4) = X3 := superpose eq10 eq10
  have eq21 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq11 eq15
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq108 eq42


@[equational_result]
theorem Equation25239_implies_Equation2 (G : Type*) [Magma G] (h : Equation25239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation25241_implies_Equation2 (G : Type*) [Magma G] (h : Equation25241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X3))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X3))) = (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X0)) = ((X4 ◇ (X4 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3))))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X4)) := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X0)) = ((X4 ◇ (X4 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X4)) := superpose eq10 eq9
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq7 eq9
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) = (((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X0)) ◇ X0) := superpose eq7 eq28
  have eq45 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3))) = (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X1)) ◇ X1) := superpose eq28 eq28
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq28 eq28
  have eq55 (X0 X1 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq28 eq7
  have eq57 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0))) ◇ (X1 ◇ X2)) = X1 := superpose eq28 eq7
  have eq63 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := superpose eq28 eq9
  have eq65 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq28 eq7
  have eq66 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ (X1 ◇ X4))) = ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X3 ◇ (X3 ◇ (X1 ◇ X4))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq28 eq9
  have eq90 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) = (((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) ◇ X3))) ◇ X0) := superpose eq10 eq11
  have eq98 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X3))) = (((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X0)) ◇ X0))) ◇ X2) := superpose eq28 eq11
  have eq117 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4))) := superpose eq7 eq48
  have eq173 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X4))) = (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (((X0 ◇ (X1 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X4))) ◇ X5))) ◇ X0) := superpose eq48 eq11
  have eq221 (X0 X1 X4 : G) : (X1 ◇ (X1 ◇ X0)) = ((X4 ◇ (X4 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X4)) := superpose eq117 eq23
  have eq238 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X4))) = (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) ◇ X0) := superpose eq117 eq173
  have eq239 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X4))) = ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq221 eq238
  have eq271 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq221 eq221
  have eq276 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X1)) = ((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq221
  have eq284 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0)) ◇ X0) := superpose eq28 eq221
  have eq285 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = (X3 ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq221 eq9
  have eq290 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq221 eq28
  have eq312 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X1)) = (X3 ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq276 eq285
  have eq314 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X3))) = (((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X0)))) ◇ X2) := superpose eq312 eq98
  have eq320 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) := superpose eq312 eq63
  have eq331 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) = (((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0))) ◇ X0) := superpose eq312 eq90
  have eq337 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq312 eq12
  have eq345 (X0 X1 X2 X4 : G) : (X1 ◇ (X1 ◇ X0)) = ((X4 ◇ (X4 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X4)) := superpose eq312 eq22
  have eq353 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ X0) := superpose eq312 eq37
  have eq357 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq312 eq65
  have eq358 (X0 X1 X3 X4 : G) : (X3 ◇ (X3 ◇ (X1 ◇ X4))) = ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (X3 ◇ (X1 ◇ X4))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq312 eq66
  have eq370 (X0 X1 X3 X4 : G) : ((X0 ◇ (X1 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X4))) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq312 eq239
  have eq392 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)))) ◇ (X1 ◇ X2)) = X1 := superpose eq312 eq57
  have eq398 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X3))) = (((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))))) ◇ X2) := superpose eq312 eq314
  have eq399 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X3))) = (((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X2) := superpose eq312 eq398
  have eq400 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) ◇ X2) := superpose eq312 eq399
  have eq403 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3))) = (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1) := superpose eq400 eq45
  have eq408 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq400 eq55
  have eq412 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq400 eq403
  have eq420 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq312 eq320
  have eq421 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq312 eq420
  have eq440 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) = (((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0))) ◇ X0) := superpose eq312 eq331
  have eq441 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) = (((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) ◇ X0) := superpose eq312 eq440
  have eq442 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) = (((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) ◇ X1)) ◇ X0) := superpose eq312 eq441
  have eq443 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X1)) ◇ X0) := superpose eq312 eq442
  have eq455 (X0 X1 X2 X4 : G) : (X1 ◇ (X1 ◇ X0)) = ((X4 ◇ (X4 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X4)) := superpose eq312 eq345
  have eq461 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq312 eq357
  have eq462 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq312 eq461
  have eq463 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq312 eq462
  have eq464 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (X3 ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq312 eq358
  have eq465 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = ((((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X3 ◇ (X3 ◇ X1)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq421 eq464
  have eq471 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq370 eq412
  have eq473 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = ((((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X3 ◇ (X3 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq471 eq465
  have eq474 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq471 eq463
  have eq476 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq471 eq421
  have eq478 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X0) ◇ X0) := superpose eq471 eq284
  have eq480 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X0) := superpose eq471 eq353
  have eq487 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) := superpose eq312 eq478
  have eq488 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq312 eq487
  have eq489 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) := superpose eq488 eq443
  have eq491 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq312 eq480
  have eq492 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq491 eq489
  have eq513 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2)) = X1 := superpose eq312 eq392
  have eq514 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) = X1 := superpose eq312 eq513
  have eq521 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq471 eq290
  have eq522 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq312 eq521
  have eq539 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq221 eq408
  have eq545 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq312 eq539
  have eq551 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq221 eq455
  have eq590 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq492 eq408
  have eq611 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq491 eq590
  have eq612 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq312 eq611
  have eq613 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq312 eq612
  have eq706 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq514 eq312
  have eq746 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq706 eq522
  have eq823 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq514 eq545
  have eq830 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq221 eq545
  have eq860 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq551 eq823
  have eq864 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq860 eq746
  have eq879 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq551 eq830
  have eq881 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq879 eq864
  have eq882 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X2 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq881 eq337
  have eq899 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X2 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq881 eq882
  have eq900 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq899 eq474
  have eq903 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq900 eq471
  have eq905 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = ((((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X3 ◇ (X3 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq900 eq473
  have eq906 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq900 eq476
  have eq921 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq900 eq488
  have eq931 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq900 eq613
  have eq945 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = ((((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq881 eq905
  have eq946 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) := superpose eq881 eq906
  have eq947 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq946 eq945
  have eq977 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq545 eq931
  have eq978 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq977 eq921
  have eq1000 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq978 eq903
  have eq1026 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq1000 eq947
  have eq1030 (X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = X1 := superpose eq977 eq1026
  have eq1033 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) = X1 := superpose eq1030 eq271
  have eq1034 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X1 ◇ X2))) = X1 := superpose eq1030 eq312
  have eq1069 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq1030 eq1033
  have eq1070 (X1 X3 : G) : (X3 ◇ X1) = X1 := superpose eq1069 eq1034
  have eq1071 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq1070 eq978
  have eq1076 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq1070 eq1071
  have eq1077 (X0 X3 : G) : X0 = X3 := superpose eq1076 eq1076
  have eq1082 (X0 : G) : sK0 ≠ X0 := superpose eq1077 eq8
  subsumption eq1082 eq1077


@[equational_result]
theorem Equation25242_implies_Equation2 (G : Type*) [Magma G] (h : Equation25242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X3))) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq26 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = (((X4 ◇ (X4 ◇ (X0 ◇ X2))) ◇ X0) ◇ (X0 ◇ X2)) := superpose eq7 eq10
  have eq44 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := superpose eq9 eq26
  have eq57 (X0 X1 X2 X5 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X5))) = X2 := superpose eq44 eq44
  have eq67 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq44 eq44
  have eq84 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq67 eq9
  have eq112 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq84 eq57
  have eq115 (X0 X3 : G) : X0 = X3 := superpose eq84 eq112
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq115 eq8
  subsumption eq138 eq115


@[equational_result]
theorem Equation25243_implies_Equation2 (G : Type*) [Magma G] (h : Equation25243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X3))) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X3))) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4))) ◇ X0) := superpose eq7 eq7
  have eq26 (X0 X1 X2 X3 X5 X6 : G) : (X1 ◇ (X1 ◇ X0)) = ((X5 ◇ (X5 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X6)) := superpose eq10 eq9
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = ((X3 ◇ (X3 ◇ X0)) ◇ X0) := superpose eq7 eq9
  have eq50 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = (((X4 ◇ (X4 ◇ (X0 ◇ X5))) ◇ X0) ◇ (X0 ◇ X2)) := superpose eq7 eq31
  have eq60 (X0 X1 X2 X4 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X2 ◇ X4)) = X2 := superpose eq31 eq7
  have eq82 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ (X4 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) ◇ (X1 ◇ X5)) = X1 := superpose eq31 eq7
  have eq88 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := superpose eq10 eq50
  have eq90 (X0 X1 X2 X6 : G) : (X1 ◇ (X1 ◇ X0)) = (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X6)) := superpose eq88 eq26
  have eq98 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X3))) = (X2 ◇ X0) := superpose eq88 eq11
  have eq104 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq98 eq7
  have eq134 (X0 X1 X2 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X4)) = X2 := superpose eq90 eq60
  have eq141 (X0 X1 X5 : G) : (X0 ◇ (X1 ◇ X5)) = X1 := superpose eq134 eq82
  have eq142 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq141 eq98
  have eq164 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq142 eq104
  have eq170 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq142 eq164
  have eq189 (X0 X1 : G) : X0 = X1 := superpose eq170 eq142
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq189 eq8
  subsumption eq191 eq189


@[equational_result]
theorem Equation25245_implies_Equation2 (G : Type*) [Magma G] (h : Equation25245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X3))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := superpose eq7 eq9
  have eq26 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2)) = X3 := superpose eq9 eq7
  have eq34 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = X3 := superpose eq22 eq26
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq7 eq34
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq130 eq53


@[equational_result]
theorem Equation25247_implies_Equation2 (G : Type*) [Magma G] (h : Equation25247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X3))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X4)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) = (((X2 ◇ (X2 ◇ (X0 ◇ X5))) ◇ X0) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X5))) ◇ X6)) := superpose eq7 eq9
  have eq31 (X0 X1 X2 X3 X4 X6 : G) : ((X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)))) ◇ (X3 ◇ X6)) = X4 := superpose eq9 eq7
  have eq36 (X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) = X2 := superpose eq10 eq19
  have eq40 (X0 X3 X4 X6 : G) : (X0 ◇ (X3 ◇ X6)) = X4 := superpose eq36 eq31
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq40
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq158 eq68


@[equational_result]
theorem Equation25251_implies_Equation2 (G : Type*) [Magma G] (h : Equation25251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X4)))))) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) ◇ X0) = X3 := superpose eq7 eq10
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (((X3 ◇ (X3 ◇ (X4 ◇ X0))) ◇ X4) ◇ X0)))) ◇ X5) = X2 := superpose eq10 eq11
  have eq47 (X0 X1 X2 X5 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X5) = X2 := superpose eq18 eq30
  have eq49 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq47 eq18
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq49
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq148 eq52


@[equational_result]
theorem Equation25253_implies_Equation2 (G : Type*) [Magma G] (h : Equation25253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ (X4 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 X6 : G) : ((X0 ◇ (X0 ◇ (X4 ◇ X5))) ◇ X6) = X4 := superpose eq7 eq12
  have eq25 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2))))) = X3 := superpose eq13 eq10
  have eq43 (X0 X7 : G) : X0 = X7 := superpose eq12 eq25
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq65 eq43


@[equational_result]
theorem Equation25254_implies_Equation2 (G : Type*) [Magma G] (h : Equation25254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation25255_implies_Equation2 (G : Type*) [Magma G] (h : Equation25255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X1 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq64 eq14


@[equational_result]
theorem Equation25256_implies_Equation2 (G : Type*) [Magma G] (h : Equation25256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation25259_implies_Equation2 (G : Type*) [Magma G] (h : Equation25259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X0))) = ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))))) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) ◇ X1) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X3)) = X1 := superpose eq10 eq7
  have eq22 (X0 X1 X2 X4 X5 : G) : (X0 ◇ X1) = (((X4 ◇ (X4 ◇ (X4 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))))) ◇ ((X4 ◇ (X4 ◇ (X4 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0))))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq9 eq9
  have eq25 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) = (((X3 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))))) ◇ ((X3 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))))) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq36 (X0 X2 : G) : ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) = X0 := superpose eq16 eq25
  have eq37 (X0 X1 X4 X5 : G) : (X0 ◇ X1) = (((X4 ◇ (X4 ◇ (X4 ◇ X0))) ◇ ((X4 ◇ (X4 ◇ (X4 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq36 eq22
  have eq39 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq36 eq13
  have eq45 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq36 eq37
  have eq48 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq39 eq7
  have eq49 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X0) := superpose eq39 eq10
  have eq52 (X0 X2 : G) : ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq39 eq36
  have eq53 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq39 eq49
  have eq88 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq39 eq53
  have eq107 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq52 eq53
  have eq123 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq107 eq45
  have eq125 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq107 eq39
  have eq133 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ X0) := superpose eq123 eq125
  have eq134 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq107 eq133
  have eq135 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq134
  have eq136 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq135 eq88
  have eq145 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq135 eq45
  have eq152 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq145 eq136
  have eq156 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq152 eq53
  have eq162 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq152 eq156
  have eq163 (X0 X1 : G) : X0 = X1 := superpose eq135 eq162
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq163 eq8
  subsumption eq176 eq163


@[equational_result]
theorem Equation25262_implies_Equation2 (G : Type*) [Magma G] (h : Equation25262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0))) ◇ X0)) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0))) ◇ X3)) = X2 := superpose eq10 eq7
  have eq42 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ X3)) ◇ X1) = X4 := superpose eq9 eq10
  have eq51 (X1 X4 : G) : (X1 ◇ X1) = X4 := superpose eq16 eq42
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq7 eq51
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq143 eq53


@[equational_result]
theorem Equation25264_implies_Equation2 (G : Type*) [Magma G] (h : Equation25264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X4) = X3 := superpose eq7 eq11
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq12 eq9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := superpose eq12 eq10
  have eq25 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq24 eq23
  have eq26 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq25 eq11
  have eq30 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq25 eq26
  have eq31 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq25 eq30
  have eq47 (X0 X1 : G) : X0 = X1 := superpose eq25 eq31
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq57 eq47


@[equational_result]
theorem Equation25265_implies_Equation2 (G : Type*) [Magma G] (h : Equation25265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = ((((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X2 ◇ X2)) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq7 eq10
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) := superpose eq7 eq9
  have eq28 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X1) := superpose eq9 eq9
  have eq31 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ (X3 ◇ X4))) = (((X3 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X4) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ (X2 ◇ X2))) := superpose eq9 eq10
  have eq35 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ (X0 ◇ X0))) = (((((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) := superpose eq9 eq10
  have eq37 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X3 ◇ X3)) := superpose eq7 eq26
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) ◇ (X2 ◇ X2)) := superpose eq28 eq10
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) = X1 := superpose eq28 eq7
  have eq58 (X0 X1 X2 X4 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ (X0 ◇ X0))) = (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ (X4 ◇ X4)) := superpose eq46 eq35
  have eq82 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X3 ◇ X3)) = X2 := superpose eq37 eq7
  have eq176 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X0))) = ((X2 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ (X3 ◇ X3)) := superpose eq15 eq7
  have eq199 (X0 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq82 eq176
  have eq202 (X1 X2 X4 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) = (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) ◇ (X4 ◇ X4)) := superpose eq199 eq58
  have eq210 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = X1 := superpose eq199 eq45
  have eq237 (X0 X1 X3 X4 : G) : (X3 ◇ (X3 ◇ (X3 ◇ X4))) = (((X3 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X4) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))) := superpose eq202 eq31
  have eq250 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) = X2 := superpose eq210 eq82
  have eq263 (X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X2))) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2)) := superpose eq250 eq202
  have eq272 (X0 X1 X3 X4 : G) : (X3 ◇ (X3 ◇ (X3 ◇ X4))) = (((X3 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X4) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq263 eq237
  have eq279 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X2)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq272 eq13
  have eq284 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq7 eq279
  have eq287 (X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X2))) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2) := superpose eq284 eq263
  have eq289 (X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X2))) = X2 := superpose eq284 eq287
  have eq290 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq289 eq7
  have eq298 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq290 eq199
  have eq301 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X1 := superpose eq298 eq210
  have eq311 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq298 eq301
  have eq312 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq311 eq289
  have eq316 (X0 X2 : G) : X0 = X2 := superpose eq312 eq312
  have eq336 (X0 : G) : sK0 ≠ X0 := superpose eq316 eq8
  subsumption eq336 eq316


@[equational_result]
theorem Equation25266_implies_Equation2 (G : Type*) [Magma G] (h : Equation25266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq60 eq18


@[equational_result]
theorem Equation25269_implies_Equation2 (G : Type*) [Magma G] (h : Equation25269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq14
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq14 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation25271_implies_Equation2 (G : Type*) [Magma G] (h : Equation25271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation25272_implies_Equation2 (G : Type*) [Magma G] (h : Equation25272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25274_implies_Equation2 (G : Type*) [Magma G] (h : Equation25274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25275_implies_Equation2 (G : Type*) [Magma G] (h : Equation25275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25276_implies_Equation2 (G : Type*) [Magma G] (h : Equation25276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25278_implies_Equation2 (G : Type*) [Magma G] (h : Equation25278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X3))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) = (((X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X4))) ◇ X3) := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3))) ◇ X2) := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) = (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) ◇ X1) := superpose eq7 eq11
  have eq22 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X4))) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) ◇ X0))) ◇ X1) := superpose eq11 eq11
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq11 eq11
  have eq29 (X0 X1 X2 X4 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0)) ◇ (X4 ◇ X1)) = X4 := superpose eq11 eq7
  have eq31 (X0 X1 X2 X4 : G) : ((X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0))) ◇ (X4 ◇ X1)) = X4 := superpose eq11 eq7
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq15 eq12
  have eq37 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) = (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X1) := superpose eq34 eq21
  have eq40 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0))) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)))) = X3 := superpose eq7 eq10
  have eq48 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X0) := superpose eq10 eq10
  have eq50 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X3))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0)) = X1 := superpose eq11 eq10
  have eq60 (X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) = X3 := superpose eq34 eq40
  have eq61 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) = X3 := superpose eq10 eq60
  have eq107 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq27 eq10
  have eq234 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X2))) ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = X3 := superpose eq10 eq29
  have eq239 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3))) ◇ X2)) ◇ X0) = (X1 ◇ (((X4 ◇ X1) ◇ ((X4 ◇ X1) ◇ ((X4 ◇ X1) ◇ X5))) ◇ X4)) := superpose eq29 eq29
  have eq278 (X0 X1 X3 : G) : (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = X3 := superpose eq37 eq234
  have eq279 (X0 X1 X3 : G) : ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = X3 := superpose eq61 eq278
  have eq280 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) = X3 := superpose eq107 eq279
  have eq328 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X3 := superpose eq7 eq31
  have eq379 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X3 := superpose eq34 eq328
  have eq431 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq10 eq280
  have eq434 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3))) ◇ X2)) := superpose eq29 eq280
  have eq480 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq431 eq15
  have eq481 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq431 eq34
  have eq484 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X0) := superpose eq431 eq48
  have eq485 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0)) = X1 := superpose eq431 eq50
  have eq488 (X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) = X3 := superpose eq431 eq61
  have eq511 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X3 := superpose eq431 eq379
  have eq519 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X0) := superpose eq431 eq484
  have eq530 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X3 := superpose eq488 eq511
  have eq531 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ X0) := superpose eq530 eq519
  have eq534 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3))) ◇ X2) = (X0 ◇ X0) := superpose eq531 eq480
  have eq535 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) = (X1 ◇ X1) := superpose eq531 eq481
  have eq538 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0)) = X1 := superpose eq531 eq485
  have eq604 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq534 eq434
  have eq605 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq604
  have eq606 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq605 eq531
  have eq612 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) = X1 := superpose eq606 eq535
  have eq615 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0)) = X1 := superpose eq606 eq538
  have eq664 (X1 X2 X4 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X4))) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X1) := superpose eq615 eq22
  have eq670 (X0 X1 X4 X5 : G) : (X1 ◇ (((X4 ◇ X1) ◇ ((X4 ◇ X1) ◇ ((X4 ◇ X1) ◇ X5))) ◇ X4)) = ((X0 ◇ X1) ◇ X0) := superpose eq615 eq239
  have eq699 (X1 X2 X4 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X4))) = ((X1 ◇ X2) ◇ X1) := superpose eq606 eq664
  have eq702 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq615 eq670
  have eq705 (X2 X4 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X4))) = X2 := superpose eq702 eq699
  have eq734 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq705 eq612
  have eq1016 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq734 eq702
  have eq1019 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq606 eq1016
  have eq1021 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq1019 eq702
  have eq1024 (X0 X2 : G) : X0 = X2 := superpose eq1021 eq1021
  have eq1029 (X0 : G) : sK0 ≠ X0 := superpose eq1024 eq8
  subsumption eq1029 eq1024


@[equational_result]
theorem Equation25280_implies_Equation2 (G : Type*) [Magma G] (h : Equation25280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq14
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq14 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation25282_implies_Equation2 (G : Type*) [Magma G] (h : Equation25282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25283_implies_Equation2 (G : Type*) [Magma G] (h : Equation25283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation25284_implies_Equation2 (G : Type*) [Magma G] (h : Equation25284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25286_implies_Equation2 (G : Type*) [Magma G] (h : Equation25286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25287_implies_Equation2 (G : Type*) [Magma G] (h : Equation25287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25288_implies_Equation2 (G : Type*) [Magma G] (h : Equation25288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25290_implies_Equation2 (G : Type*) [Magma G] (h : Equation25290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25291_implies_Equation2 (G : Type*) [Magma G] (h : Equation25291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25292_implies_Equation2 (G : Type*) [Magma G] (h : Equation25292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25293_implies_Equation2 (G : Type*) [Magma G] (h : Equation25293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25295_implies_Equation2 (G : Type*) [Magma G] (h : Equation25295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X0))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X0)))))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq9 eq9
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : (((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := superpose eq9 eq7
  have eq63 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X0)))))) = ((X0 ◇ (X0 ◇ (X4 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X0))))))))) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X0)))) := superpose eq7 eq11
  have eq102 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq14
  have eq103 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq14 eq9
  have eq151 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = ((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ (X4 ◇ X2)))) ◇ (X0 ◇ X1)) := superpose eq16 eq16
  have eq152 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X1)) := superpose eq9 eq16
  have eq156 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)))))) = X0 := superpose eq16 eq10
  have eq180 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) := superpose eq152 eq151
  have eq232 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq180 eq156
  have eq260 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq14 eq232
  have eq262 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq232 eq232
  have eq265 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq232
  have eq267 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))) = X0 := superpose eq232 eq10
  have eq269 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq232 eq11
  have eq270 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq232 eq10
  have eq271 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq232 eq7
  have eq283 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq260
  have eq291 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = (((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X2) := superpose eq9 eq17
  have eq292 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq14 eq17
  have eq336 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = (((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) ◇ X2) := superpose eq180 eq291
  have eq337 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq180 eq292
  have eq338 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq103 eq337
  have eq345 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq338 eq269
  have eq346 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq338 eq271
  have eq347 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq338 eq265
  have eq348 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq338 eq283
  have eq353 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq346 eq270
  have eq354 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq347 eq102
  have eq355 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq338 eq354
  have eq357 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq355 eq345
  have eq359 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X1) ◇ X0) := superpose eq338 eq357
  have eq366 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq348 eq14
  have eq368 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq366 eq267
  have eq370 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq366 eq368
  have eq371 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq338 eq370
  have eq372 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq371 eq262
  have eq383 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = (((X2 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) ◇ X2) := superpose eq372 eq336
  have eq398 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq372 eq353
  have eq400 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq372 eq17
  have eq406 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X0))))) = ((X0 ◇ (X0 ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ X0)))))))) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X0)))) := superpose eq372 eq63
  have eq420 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq372 eq7
  have eq432 (X0 X1 X2 : G) : (((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq372 eq19
  have eq437 (X0 X2 X3 : G) : (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) := superpose eq372 eq180
  have eq442 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq372 eq359
  have eq445 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) := superpose eq372 eq383
  have eq446 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X1)) = (((X2 ◇ X0) ◇ X0) ◇ X2) := superpose eq372 eq445
  have eq471 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq372 eq398
  have eq475 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0))))))) ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq372 eq406
  have eq476 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) = ((X0 ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))))) ◇ (X1 ◇ (X3 ◇ X0))) := superpose eq372 eq475
  have eq504 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq372 eq432
  have eq507 (X0 X2 X3 : G) : (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X3 ◇ X0))) := superpose eq372 eq437
  have eq508 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq507 eq400
  have eq511 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq508 eq446
  have eq519 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq511 eq504
  have eq547 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq511 eq442
  have eq549 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq547 eq471
  have eq550 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq519 eq549
  have eq554 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq550 eq420
  have eq560 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1)))) ◇ X1) := superpose eq550 eq476
  have eq600 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq550 eq554
  have eq610 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = X1 := superpose eq600 eq560
  have eq611 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq550 eq610
  have eq612 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq550 eq611
  have eq613 (X0 X3 : G) : X0 = X3 := superpose eq612 eq612
  have eq618 (X0 : G) : sK0 ≠ X0 := superpose eq613 eq8
  subsumption eq618 eq613


@[equational_result]
theorem Equation25297_implies_Equation2 (G : Type*) [Magma G] (h : Equation25297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X0 ◇ X4) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X4) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X4 ◇ (X4 ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X5)) := superpose eq9 eq9
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = ((X3 ◇ (X3 ◇ X1)) ◇ X0) := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X0)) = ((X3 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq32 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X5 ◇ X0)) = (((X2 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4) ◇ (X0 ◇ X1)) := superpose eq9 eq10
  have eq42 (X0 X5 : G) : (X5 ◇ (X5 ◇ X0)) = X0 := superpose eq10 eq32
  have eq53 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X5)) := superpose eq42 eq13
  have eq54 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ X0) := superpose eq42 eq17
  have eq55 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X1)) = X0 := superpose eq42 eq18
  have eq65 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X5)) := superpose eq42 eq53
  have eq66 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq42 eq55
  have eq67 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq66 eq54
  have eq70 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X1 := superpose eq67 eq65
  have eq77 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X1 := superpose eq67 eq70
  have eq78 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq67 eq77
  have eq79 (X0 X3 : G) : X0 = X3 := superpose eq78 eq78
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq84 eq79


@[equational_result]
theorem Equation25299_implies_Equation2 (G : Type*) [Magma G] (h : Equation25299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq116 eq38


@[equational_result]
theorem Equation25301_implies_Equation2 (G : Type*) [Magma G] (h : Equation25301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X4)) = X3 := superpose eq7 eq7
  have eq54 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq73 eq54


@[equational_result]
theorem Equation25305_implies_Equation2 (G : Type*) [Magma G] (h : Equation25305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq59 eq24


@[equational_result]
theorem Equation25307_implies_Equation2 (G : Type*) [Magma G] (h : Equation25307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X2) = ((X1 ◇ (X1 ◇ X0)) ◇ (X5 ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq154 eq65


@[equational_result]
theorem Equation25308_implies_Equation2 (G : Type*) [Magma G] (h : Equation25308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation25309_implies_Equation2 (G : Type*) [Magma G] (h : Equation25309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X4 ◇ X4) = ((X1 ◇ (X1 ◇ X0)) ◇ (X5 ◇ X5)) := superpose eq7 eq7
  have eq48 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq68 (X0 X2 : G) : X0 = X2 := superpose eq48 eq48
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq160 eq68


@[equational_result]
theorem Equation25310_implies_Equation2 (G : Type*) [Magma G] (h : Equation25310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation25312_implies_Equation2 (G : Type*) [Magma G] (h : Equation25312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ (X4 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X1)))) := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = ((X0 ◇ (X0 ◇ (X4 ◇ X0))) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq9 eq10
  have eq31 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X2 ◇ (X3 ◇ X2))) = (((X4 ◇ X2) ◇ ((X4 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ X4) := superpose eq10 eq10
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq10 eq10
  have eq35 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq10 eq7
  have eq50 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) := superpose eq7 eq33
  have eq55 (X0 X1 X2 X4 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (X2 ◇ (X2 ◇ (X4 ◇ X2))) := superpose eq10 eq33
  have eq91 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ (X0 ◇ (X4 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X3 ◇ X1)))) := superpose eq50 eq24
  have eq93 (X0 X1 X4 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq50 eq35
  have eq99 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = ((X0 ◇ (X0 ◇ (X4 ◇ X0))) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq50 eq25
  have eq195 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq11
  have eq202 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)) ◇ X0) := superpose eq11 eq9
  have eq239 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X0 ◇ X1)) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))))) = X4 := superpose eq13 eq14
  have eq286 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) = (((X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X3)) ◇ X3) := superpose eq11 eq15
  have eq336 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)))) ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X3 ◇ X2)) = X3 := superpose eq15 eq93
  have eq343 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) := superpose eq202 eq286
  have eq345 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq343 eq195
  have eq377 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X3 ◇ X2)) = X3 := superpose eq343 eq336
  have eq378 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (X3 ◇ X2)) = X3 := superpose eq99 eq377
  have eq379 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X2)) = X3 := superpose eq345 eq378
  have eq397 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq379
  have eq443 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq343 eq397
  have eq444 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq443 eq91
  have eq447 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq444 eq9
  have eq519 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq447 eq7
  have eq522 (X0 X2 X3 X4 : G) : (X2 ◇ (X2 ◇ (X3 ◇ X2))) = (((X4 ◇ X2) ◇ ((X4 ◇ X2) ◇ X0)) ◇ X4) := superpose eq447 eq31
  have eq524 (X0 X2 X4 : G) : (X2 ◇ (X2 ◇ (X4 ◇ X2))) = (X2 ◇ (X2 ◇ X0)) := superpose eq447 eq55
  have eq535 (X0 X1 X2 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X4 ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)))) = X4 := superpose eq447 eq239
  have eq545 (X0 X2 X4 : G) : (((X4 ◇ X2) ◇ ((X4 ◇ X2) ◇ X0)) ◇ X4) = X2 := superpose eq447 eq522
  have eq546 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = X2 := superpose eq447 eq524
  have eq547 (X2 X4 : G) : ((X4 ◇ X2) ◇ X4) = X2 := superpose eq546 eq545
  have eq564 (X0 X1 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X0))) = X4 := superpose eq546 eq535
  have eq565 (X0 X1 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X1)) = X4 := superpose eq547 eq564
  have eq566 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X4 := superpose eq519 eq565
  have eq567 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq566 eq447
  have eq569 (X0 X2 : G) : X0 = X2 := superpose eq519 eq567
  have eq576 (X0 : G) : sK0 ≠ X0 := superpose eq569 eq8
  subsumption eq576 eq569


@[equational_result]
theorem Equation25314_implies_Equation2 (G : Type*) [Magma G] (h : Equation25314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq34 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq10
  have eq69 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq34 eq34
  have eq74 (X0 X3 : G) : X0 = X3 := superpose eq69 eq69
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq118 eq74


@[equational_result]
theorem Equation25316_implies_Equation2 (G : Type*) [Magma G] (h : Equation25316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25317_implies_Equation2 (G : Type*) [Magma G] (h : Equation25317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25318_implies_Equation2 (G : Type*) [Magma G] (h : Equation25318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25320_implies_Equation2 (G : Type*) [Magma G] (h : Equation25320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation25321_implies_Equation2 (G : Type*) [Magma G] (h : Equation25321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25322_implies_Equation2 (G : Type*) [Magma G] (h : Equation25322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25324_implies_Equation2 (G : Type*) [Magma G] (h : Equation25324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25325_implies_Equation2 (G : Type*) [Magma G] (h : Equation25325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25326_implies_Equation2 (G : Type*) [Magma G] (h : Equation25326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25327_implies_Equation2 (G : Type*) [Magma G] (h : Equation25327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25331_implies_Equation2 (G : Type*) [Magma G] (h : Equation25331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq32 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq10
  have eq62 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq32 eq32
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq62 eq62
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq104 eq67


@[equational_result]
theorem Equation25333_implies_Equation2 (G : Type*) [Magma G] (h : Equation25333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25334_implies_Equation2 (G : Type*) [Magma G] (h : Equation25334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25335_implies_Equation2 (G : Type*) [Magma G] (h : Equation25335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25337_implies_Equation2 (G : Type*) [Magma G] (h : Equation25337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25338_implies_Equation2 (G : Type*) [Magma G] (h : Equation25338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation25339_implies_Equation2 (G : Type*) [Magma G] (h : Equation25339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25341_implies_Equation2 (G : Type*) [Magma G] (h : Equation25341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25342_implies_Equation2 (G : Type*) [Magma G] (h : Equation25342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25343_implies_Equation2 (G : Type*) [Magma G] (h : Equation25343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25344_implies_Equation2 (G : Type*) [Magma G] (h : Equation25344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25346_implies_Equation2 (G : Type*) [Magma G] (h : Equation25346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ (X4 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq10
  have eq52 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq23 eq23
  have eq76 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq52 eq7
  have eq80 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X4 := superpose eq52 eq23
  have eq99 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq80 eq52
  have eq101 (X0 X2 : G) : X0 = X2 := superpose eq76 eq99
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq101 eq8
  subsumption eq114 eq101


@[equational_result]
theorem Equation25347_implies_Equation2 (G : Type*) [Magma G] (h : Equation25347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X3)) = X5 := superpose eq10 eq7
  have eq25 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X0) = ((X4 ◇ (X4 ◇ (X5 ◇ X6))) ◇ X2) := superpose eq10 eq7
  have eq30 (X0 X1 X2 X5 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X5 ◇ X2)) = X5 := superpose eq7 eq11
  have eq49 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X0) = (X4 ◇ (X4 ◇ ((X2 ◇ X5) ◇ X6))) := superpose eq11 eq7
  have eq51 (X3 X5 : G) : (X3 ◇ (X5 ◇ X3)) = X5 := superpose eq30 eq24
  have eq60 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) := superpose eq10 eq51
  have eq61 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq51 eq51
  have eq76 (X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) = X1 := superpose eq61 eq60
  have eq82 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X0) = X2 := superpose eq76 eq25
  have eq86 (X2 X4 X5 X6 : G) : (X4 ◇ (X4 ◇ ((X2 ◇ X5) ◇ X6))) = X2 := superpose eq82 eq49
  have eq90 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq86 eq82
  have eq110 (X0 X2 : G) : X0 = X2 := superpose eq90 eq90
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq110 eq8
  subsumption eq112 eq110


@[equational_result]
theorem Equation25348_implies_Equation2 (G : Type*) [Magma G] (h : Equation25348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq34 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq10
  have eq77 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq34 eq34
  have eq82 (X0 X3 : G) : X0 = X3 := superpose eq77 eq77
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq119 eq82


@[equational_result]
theorem Equation25349_implies_Equation2 (G : Type*) [Magma G] (h : Equation25349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 X6 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq32 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq10
  have eq62 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq32 eq32
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq62 eq62
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq104 eq67


@[equational_result]
theorem Equation25351_implies_Equation2 (G : Type*) [Magma G] (h : Equation25351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25352_implies_Equation2 (G : Type*) [Magma G] (h : Equation25352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25353_implies_Equation2 (G : Type*) [Magma G] (h : Equation25353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25354_implies_Equation2 (G : Type*) [Magma G] (h : Equation25354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25356_implies_Equation2 (G : Type*) [Magma G] (h : Equation25356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25357_implies_Equation2 (G : Type*) [Magma G] (h : Equation25357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25358_implies_Equation2 (G : Type*) [Magma G] (h : Equation25358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25359_implies_Equation2 (G : Type*) [Magma G] (h : Equation25359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25361_implies_Equation2 (G : Type*) [Magma G] (h : Equation25361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25362_implies_Equation2 (G : Type*) [Magma G] (h : Equation25362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25363_implies_Equation2 (G : Type*) [Magma G] (h : Equation25363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25364_implies_Equation2 (G : Type*) [Magma G] (h : Equation25364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25366_implies_Equation2 (G : Type*) [Magma G] (h : Equation25366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25367_implies_Equation2 (G : Type*) [Magma G] (h : Equation25367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25368_implies_Equation2 (G : Type*) [Magma G] (h : Equation25368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25369_implies_Equation2 (G : Type*) [Magma G] (h : Equation25369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25370_implies_Equation2 (G : Type*) [Magma G] (h : Equation25370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25372_implies_Equation2 (G : Type*) [Magma G] (h : Equation25372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X0))) = (((X0 ◇ X1) ◇ (X2 ◇ ((X1 ◇ (X3 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X3 ◇ (X0 ◇ X0)))))) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose eq9 eq7
  have eq55 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = ((((X0 ◇ X0) ◇ X1) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))))) ◇ (X0 ◇ X0)) := superpose eq9 eq11
  have eq68 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))))) = X3 := superpose eq11 eq10
  have eq69 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) ◇ (X2 ◇ X3)) = X2 := superpose eq11 eq7
  have eq78 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))))) = X3 := superpose eq9 eq68
  have eq79 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X3)) = X2 := superpose eq9 eq69
  have eq125 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq17 eq79
  have eq146 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq125 eq55
  have eq179 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq146 eq78
  have eq188 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq146 eq179
  have eq232 (X0 X1 : G) : X0 = X1 := superpose eq9 eq188
  have eq252 (X0 : G) : sK0 ≠ X0 := superpose eq232 eq8
  subsumption eq252 eq232


@[equational_result]
theorem Equation25373_implies_Equation2 (G : Type*) [Magma G] (h : Equation25373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq10 eq9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq10 eq12
  have eq20 (X0 X2 : G) : X0 = X2 := superpose eq10 eq13
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq23 eq20


@[equational_result]
theorem Equation25374_implies_Equation2 (G : Type*) [Magma G] (h : Equation25374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25376_implies_Equation2 (G : Type*) [Magma G] (h : Equation25376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq83 eq19


@[equational_result]
theorem Equation25377_implies_Equation2 (G : Type*) [Magma G] (h : Equation25377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) = X2 := superpose eq7 eq10
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X4)) ◇ (X3 ◇ (X4 ◇ X4))))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) ◇ X3) ◇ (X5 ◇ X5))) ◇ X4) = X5 := superpose eq11 eq11
  have eq80 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq10 eq20
  have eq108 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X2 := superpose eq80 eq10
  have eq109 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) = X2 := superpose eq80 eq20
  have eq130 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X2 := superpose eq80 eq109
  have eq132 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((((X1 ◇ (X2 ◇ X4)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) ◇ X3) ◇ (X5 ◇ X5))) ◇ X4) = X5 := superpose eq130 eq45
  have eq174 (X4 X5 : G) : (X5 ◇ X4) = X5 := superpose eq130 eq132
  have eq177 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X2 := superpose eq174 eq108
  have eq188 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq174 eq177
  have eq189 (X0 X3 : G) : X0 = X3 := superpose eq188 eq188
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq189 eq8
  subsumption eq191 eq189


@[equational_result]
theorem Equation25378_implies_Equation2 (G : Type*) [Magma G] (h : Equation25378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq67 eq19


@[equational_result]
theorem Equation25381_implies_Equation2 (G : Type*) [Magma G] (h : Equation25381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq34 eq13


@[equational_result]
theorem Equation25382_implies_Equation2 (G : Type*) [Magma G] (h : Equation25382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation25384_implies_Equation2 (G : Type*) [Magma G] (h : Equation25384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation25385_implies_Equation2 (G : Type*) [Magma G] (h : Equation25385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation25386_implies_Equation2 (G : Type*) [Magma G] (h : Equation25386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25387_implies_Equation2 (G : Type*) [Magma G] (h : Equation25387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25389_implies_Equation2 (G : Type*) [Magma G] (h : Equation25389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) := superpose eq9 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq16 eq10
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq9 eq17
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := superpose eq17 eq17
  have eq26 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq17 eq9
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = X1 := superpose eq9 eq22
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq9 eq24
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X1 := superpose eq27 eq26
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq28 eq30
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq43 eq38


@[equational_result]
theorem Equation25391_implies_Equation2 (G : Type*) [Magma G] (h : Equation25391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25393_implies_Equation2 (G : Type*) [Magma G] (h : Equation25393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X1))) = (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq10 eq9
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq11 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25395_implies_Equation2 (G : Type*) [Magma G] (h : Equation25395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation25399_implies_Equation2 (G : Type*) [Magma G] (h : Equation25399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation25401_implies_Equation2 (G : Type*) [Magma G] (h : Equation25401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X1)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation25402_implies_Equation2 (G : Type*) [Magma G] (h : Equation25402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) ◇ X0) = X4 := superpose eq7 eq7
  have eq41 (X0 X6 : G) : X0 = X6 := superpose eq11 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq61 eq41


@[equational_result]
theorem Equation25403_implies_Equation2 (G : Type*) [Magma G] (h : Equation25403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation25404_implies_Equation2 (G : Type*) [Magma G] (h : Equation25404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25407_implies_Equation2 (G : Type*) [Magma G] (h : Equation25407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X2))) = ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) = (X3 ◇ X0) := superpose eq9 eq10
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9
  have eq14 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq13 eq12
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq14
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq13 eq34
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq102 eq53


@[equational_result]
theorem Equation25408_implies_Equation2 (G : Type*) [Magma G] (h : Equation25408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25412_implies_Equation2 (G : Type*) [Magma G] (h : Equation25412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation25415_implies_Equation2 (G : Type*) [Magma G] (h : Equation25415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X0 ◇ X2))) = ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := superpose eq7 eq9
  have eq65 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ X0) := superpose eq23 eq22
  have eq152 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq65
  have eq286 (X0 X3 : G) : X0 = X3 := superpose eq7 eq152
  have eq475 (X0 : G) : sK0 ≠ X0 := superpose eq286 eq8
  subsumption eq475 eq286


@[equational_result]
theorem Equation25416_implies_Equation2 (G : Type*) [Magma G] (h : Equation25416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation25418_implies_Equation2 (G : Type*) [Magma G] (h : Equation25418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) ◇ X0) = X4 := superpose eq7 eq7
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq11 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation25419_implies_Equation2 (G : Type*) [Magma G] (h : Equation25419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation25420_implies_Equation2 (G : Type*) [Magma G] (h : Equation25420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq11
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq179 eq57


@[equational_result]
theorem Equation25421_implies_Equation2 (G : Type*) [Magma G] (h : Equation25421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25423_implies_Equation2 (G : Type*) [Magma G] (h : Equation25423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))))) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq10 eq7
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq7 eq11
  have eq38 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4)))) ◇ (X5 ◇ (X3 ◇ X6))) ◇ X0) = X3 := superpose eq11 eq7
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq30 eq18
  have eq57 (X0 X3 X5 : G) : (X5 ◇ X0) = X3 := superpose eq40 eq38
  have eq58 (X0 X2 : G) : X0 = X2 := superpose eq10 eq57
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq76 eq58


@[equational_result]
theorem Equation25424_implies_Equation2 (G : Type*) [Magma G] (h : Equation25424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4))))) = X0 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X3))) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X3))) = X1 := superpose eq14 eq13
  have eq21 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq19 eq10
  have eq34 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq14 eq21
  have eq36 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq34 eq19
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq11 eq36
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq56 eq37


@[equational_result]
theorem Equation25425_implies_Equation2 (G : Type*) [Magma G] (h : Equation25425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq10 eq15
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq59 eq26


@[equational_result]
theorem Equation25426_implies_Equation2 (G : Type*) [Magma G] (h : Equation25426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X6 : G) : (X0 ◇ (X4 ◇ X6)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25428_implies_Equation2 (G : Type*) [Magma G] (h : Equation25428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq83 eq19


@[equational_result]
theorem Equation25429_implies_Equation2 (G : Type*) [Magma G] (h : Equation25429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X5 ◇ (X6 ◇ ((X1 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X4)))) ◇ X7))))) = X5 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X1 := superpose eq10 eq10
  have eq45 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ (X1 ◇ (X5 ◇ (X6 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X4))) ◇ X2) ◇ X7))))) = X5 := superpose eq11 eq10
  have eq49 (X0 X1 X2 X5 X6 : G) : (X0 ◇ (X1 ◇ (X5 ◇ (X6 ◇ X2)))) = X5 := superpose eq22 eq45
  have eq50 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq49 eq14
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq50
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq145 eq56


@[equational_result]
theorem Equation25430_implies_Equation2 (G : Type*) [Magma G] (h : Equation25430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation25431_implies_Equation2 (G : Type*) [Magma G] (h : Equation25431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X6)) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation25433_implies_Equation2 (G : Type*) [Magma G] (h : Equation25433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X4))) ◇ X1)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))))) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5))) ◇ X6) ◇ X3) ◇ X0) = X2 := superpose eq10 eq10
  have eq25 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4) ◇ ((X4 ◇ X2) ◇ (X5 ◇ X6))) ◇ X0) = X5 := superpose eq10 eq7
  have eq35 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X3 := superpose eq11 eq11
  have eq50 (X0 X2 X3 X6 : G) : (((X2 ◇ X6) ◇ X3) ◇ X0) = X2 := superpose eq35 eq22
  have eq52 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq50 eq25
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq52
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq172 eq53


@[equational_result]
theorem Equation25434_implies_Equation2 (G : Type*) [Magma G] (h : Equation25434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq61 eq15


@[equational_result]
theorem Equation25435_implies_Equation2 (G : Type*) [Magma G] (h : Equation25435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq55 eq16


@[equational_result]
theorem Equation25436_implies_Equation2 (G : Type*) [Magma G] (h : Equation25436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 X6 : G) : (X0 ◇ (X2 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation25438_implies_Equation2 (G : Type*) [Magma G] (h : Equation25438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation25439_implies_Equation2 (G : Type*) [Magma G] (h : Equation25439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation25440_implies_Equation2 (G : Type*) [Magma G] (h : Equation25440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation25441_implies_Equation2 (G : Type*) [Magma G] (h : Equation25441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25443_implies_Equation2 (G : Type*) [Magma G] (h : Equation25443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : ((X1 ◇ X0) ◇ (X6 ◇ X1)) = X5 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation25444_implies_Equation2 (G : Type*) [Magma G] (h : Equation25444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 X6 : G) : (X0 ◇ (X6 ◇ X5)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation25445_implies_Equation2 (G : Type*) [Magma G] (h : Equation25445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X6 : G) : (X0 ◇ (X6 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25446_implies_Equation2 (G : Type*) [Magma G] (h : Equation25446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X6 : G) : (X0 ◇ (X6 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25447_implies_Equation2 (G : Type*) [Magma G] (h : Equation25447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X5 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25449_implies_Equation2 (G : Type*) [Magma G] (h : Equation25449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq10
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ X1) := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = (X1 ◇ X1) := superpose eq14 eq13
  have eq20 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X3 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq18 eq9
  have eq26 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq10 eq20
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq10 eq26
  have eq42 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq35
  have eq72 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq42 eq12
  have eq78 (X0 X1 : G) : X0 = X1 := superpose eq10 eq72
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq91 eq78


@[equational_result]
theorem Equation25450_implies_Equation2 (G : Type*) [Magma G] (h : Equation25450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X3 ◇ X0))) = ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X0)))))) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) := superpose eq10 eq10
  have eq73 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X4))) = (((X5 ◇ (((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ X1) ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4))))))))) ◇ ((X4 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))))))) ◇ X4) := superpose eq11 eq11
  have eq74 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq10 eq11
  have eq83 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))))) = ((X3 ◇ X3) ◇ ((X4 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))))) := superpose eq11 eq10
  have eq91 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq74 eq74
  have eq105 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))))))) := superpose eq74 eq10
  have eq125 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq10 eq91
  have eq127 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq125 eq74
  have eq130 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq127 eq17
  have eq156 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = (X4 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))))) := superpose eq130 eq83
  have eq167 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X4))) = ((((X3 ◇ (X2 ◇ X4)) ◇ (X3 ◇ (X2 ◇ X4))) ◇ ((X4 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X4)))))))) ◇ X4) := superpose eq156 eq73
  have eq168 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X4))) = (((X3 ◇ (X2 ◇ X4)) ◇ (X3 ◇ (X2 ◇ X4))) ◇ X4) := superpose eq130 eq167
  have eq183 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq130 eq105
  have eq192 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X4))) = (((X2 ◇ X4) ◇ (X2 ◇ X4)) ◇ X4) := superpose eq183 eq168
  have eq195 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X4))) = ((X4 ◇ X4) ◇ X4) := superpose eq183 eq192
  have eq196 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X4))) = X4 := superpose eq127 eq195
  have eq204 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq196 eq11
  have eq258 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq196 eq204
  have eq260 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq258 eq130
  have eq277 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X2)) = X4 := superpose eq260 eq196
  have eq283 (X2 X3 X4 : G) : (X2 ◇ X3) = X4 := superpose eq260 eq277
  have eq284 (X0 X1 : G) : X0 = X1 := superpose eq258 eq283
  have eq292 (X0 : G) : sK0 ≠ X0 := superpose eq284 eq8
  subsumption eq292 eq284


@[equational_result]
theorem Equation25451_implies_Equation2 (G : Type*) [Magma G] (h : Equation25451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25453_implies_Equation2 (G : Type*) [Magma G] (h : Equation25453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq35 eq14


@[equational_result]
theorem Equation25455_implies_Equation2 (G : Type*) [Magma G] (h : Equation25455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X4)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation25459_implies_Equation2 (G : Type*) [Magma G] (h : Equation25459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq71 eq16


@[equational_result]
theorem Equation25461_implies_Equation2 (G : Type*) [Magma G] (h : Equation25461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X1)) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation25462_implies_Equation2 (G : Type*) [Magma G] (h : Equation25462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X5 X6 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X5))) ◇ X6) = X5 := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X0)) ◇ X7) = X6 := superpose eq11 eq11
  have eq25 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq12 eq15
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq142 eq58


@[equational_result]
theorem Equation25463_implies_Equation2 (G : Type*) [Magma G] (h : Equation25463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation25464_implies_Equation2 (G : Type*) [Magma G] (h : Equation25464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation25466_implies_Equation2 (G : Type*) [Magma G] (h : Equation25466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq9 eq9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq18 eq18
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq9 eq23
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq64 eq26


@[equational_result]
theorem Equation25468_implies_Equation2 (G : Type*) [Magma G] (h : Equation25468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq13 (X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq13 eq17
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq41 eq28


@[equational_result]
theorem Equation25470_implies_Equation2 (G : Type*) [Magma G] (h : Equation25470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation25471_implies_Equation2 (G : Type*) [Magma G] (h : Equation25471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25472_implies_Equation2 (G : Type*) [Magma G] (h : Equation25472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25474_implies_Equation2 (G : Type*) [Magma G] (h : Equation25474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25475_implies_Equation2 (G : Type*) [Magma G] (h : Equation25475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25476_implies_Equation2 (G : Type*) [Magma G] (h : Equation25476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25478_implies_Equation2 (G : Type*) [Magma G] (h : Equation25478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25479_implies_Equation2 (G : Type*) [Magma G] (h : Equation25479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25480_implies_Equation2 (G : Type*) [Magma G] (h : Equation25480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25481_implies_Equation2 (G : Type*) [Magma G] (h : Equation25481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25485_implies_Equation2 (G : Type*) [Magma G] (h : Equation25485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25487_implies_Equation2 (G : Type*) [Magma G] (h : Equation25487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25488_implies_Equation2 (G : Type*) [Magma G] (h : Equation25488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation25489_implies_Equation2 (G : Type*) [Magma G] (h : Equation25489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25491_implies_Equation2 (G : Type*) [Magma G] (h : Equation25491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25492_implies_Equation2 (G : Type*) [Magma G] (h : Equation25492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25493_implies_Equation2 (G : Type*) [Magma G] (h : Equation25493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25495_implies_Equation2 (G : Type*) [Magma G] (h : Equation25495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25496_implies_Equation2 (G : Type*) [Magma G] (h : Equation25496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25497_implies_Equation2 (G : Type*) [Magma G] (h : Equation25497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25498_implies_Equation2 (G : Type*) [Magma G] (h : Equation25498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25500_implies_Equation2 (G : Type*) [Magma G] (h : Equation25500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X4 ◇ X0)) ◇ (X5 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ X1) := superpose eq10 eq10
  have eq18 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (X1 ◇ X1) := superpose eq14 eq13
  have eq20 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ (X4 ◇ X0)) ◇ (X5 ◇ (X1 ◇ X1))) = X5 := superpose eq18 eq9
  have eq26 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq10 eq20
  have eq42 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq26
  have eq52 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq42 eq26
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq10 eq52
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq80 eq56


@[equational_result]
theorem Equation25501_implies_Equation2 (G : Type*) [Magma G] (h : Equation25501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X4 ◇ X0)) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ (X4 ◇ X5))) = ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X4 ◇ X6))))) = X3 := superpose eq10 eq10
  have eq20 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X4 := superpose eq10 eq7
  have eq45 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) ◇ X0) = ((X4 ◇ (X5 ◇ (X4 ◇ X6))) ◇ (X2 ◇ X7)) := superpose eq9 eq7
  have eq50 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X5)) := superpose eq9 eq20
  have eq51 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq20 eq20
  have eq63 (X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X5)) = X1 := superpose eq51 eq50
  have eq70 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) ◇ X0) = X2 := superpose eq63 eq45
  have eq74 (X2 X4 X5 : G) : (X4 ◇ (X2 ◇ (X4 ◇ X5))) = X2 := superpose eq70 eq11
  have eq77 (X1 X3 X4 X5 X6 : G) : (X1 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X4 ◇ X6))))) = X3 := superpose eq74 eq12
  have eq86 (X1 X3 X5 : G) : (X1 ◇ (X3 ◇ X5)) = X3 := superpose eq74 eq77
  have eq90 (X2 X4 : G) : (X4 ◇ X4) = X2 := superpose eq86 eq74
  have eq94 (X0 X2 : G) : X0 = X2 := superpose eq90 eq90
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq99 eq94


@[equational_result]
theorem Equation25502_implies_Equation2 (G : Type*) [Magma G] (h : Equation25502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X4 ◇ X3))) = ((X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq21 (X0 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X4 ◇ X3))) = (X2 ◇ X0) := superpose eq12 eq11
  have eq22 (X0 X2 X4 : G) : (X4 ◇ X4) = (X2 ◇ X0) := superpose eq12 eq21
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq22
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq10 eq24
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq66 eq36


@[equational_result]
theorem Equation25503_implies_Equation2 (G : Type*) [Magma G] (h : Equation25503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X6 X7 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X4 ◇ X0)) ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq7
  have eq13 (X4 X6 X7 : G) : (X4 ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq13 eq17
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq41 eq28


@[equational_result]
theorem Equation25505_implies_Equation2 (G : Type*) [Magma G] (h : Equation25505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25506_implies_Equation2 (G : Type*) [Magma G] (h : Equation25506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25507_implies_Equation2 (G : Type*) [Magma G] (h : Equation25507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25508_implies_Equation2 (G : Type*) [Magma G] (h : Equation25508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25510_implies_Equation2 (G : Type*) [Magma G] (h : Equation25510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25511_implies_Equation2 (G : Type*) [Magma G] (h : Equation25511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25512_implies_Equation2 (G : Type*) [Magma G] (h : Equation25512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25513_implies_Equation2 (G : Type*) [Magma G] (h : Equation25513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25515_implies_Equation2 (G : Type*) [Magma G] (h : Equation25515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25516_implies_Equation2 (G : Type*) [Magma G] (h : Equation25516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25517_implies_Equation2 (G : Type*) [Magma G] (h : Equation25517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25518_implies_Equation2 (G : Type*) [Magma G] (h : Equation25518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25520_implies_Equation2 (G : Type*) [Magma G] (h : Equation25520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25521_implies_Equation2 (G : Type*) [Magma G] (h : Equation25521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25522_implies_Equation2 (G : Type*) [Magma G] (h : Equation25522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25523_implies_Equation2 (G : Type*) [Magma G] (h : Equation25523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25524_implies_Equation2 (G : Type*) [Magma G] (h : Equation25524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25527_implies_Equation2 (G : Type*) [Magma G] (h : Equation25527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ X3) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq13 eq12
  have eq20 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X1 ◇ (X3 ◇ X0)) ◇ ((X0 ◇ X3) ◇ X3)) := superpose eq18 eq9
  have eq25 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = ((X3 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X1 ◇ X0)))) := superpose eq20 eq20
  have eq30 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq20 eq10
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X1 := superpose eq13 eq30
  have eq32 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = ((X3 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq31 eq25
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq31 eq32
  have eq36 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq31 eq35
  have eq38 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq36 eq10
  have eq43 (X0 X2 : G) : X0 = X2 := superpose eq38 eq38
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation25528_implies_Equation2 (G : Type*) [Magma G] (h : Equation25528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq10 eq16
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation25531_implies_Equation2 (G : Type*) [Magma G] (h : Equation25531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X1 ◇ X2) ◇ ((X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0)) ◇ X1)) := superpose eq7 eq10
  have eq44 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq7 eq14
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq11 eq14
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = (X0 ◇ (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq7 eq45
  have eq55 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))) := superpose eq7 eq9
  have eq58 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))))) := superpose eq10 eq9
  have eq88 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2))) ◇ X1) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2))) ◇ X1) ◇ X0)) = (X0 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq10 eq44
  have eq133 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X1 ◇ (((X2 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1))) ◇ X2) ◇ (((X2 ◇ ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1))) ◇ X2) ◇ X0))))) = X0 := superpose eq10 eq55
  have eq162 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := superpose eq88 eq133
  have eq194 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ (((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3)))))) ◇ X0) ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3)))))))) := superpose eq162 eq9
  have eq195 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3)))) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq162 eq7
  have eq220 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq58 eq7
  have eq244 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq7 eq220
  have eq252 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq244 eq10
  have eq254 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq244 eq14
  have eq260 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq244 eq9
  have eq279 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq252 eq254
  have eq280 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq252 eq279
  have eq281 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq280 eq244
  have eq318 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq281 eq260
  have eq319 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq281 eq318
  have eq320 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq281 eq319
  have eq322 (X0 X2 X3 : G) : (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3)))) := superpose eq320 eq195
  have eq370 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq322 eq194
  have eq392 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq370 eq54
  have eq448 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = X2 := superpose eq392 eq10
  have eq552 (X0 X2 : G) : X0 = X2 := superpose eq7 eq448
  have eq573 (X0 : G) : sK0 ≠ X0 := superpose eq552 eq8
  subsumption eq573 eq552


@[equational_result]
theorem Equation25532_implies_Equation2 (G : Type*) [Magma G] (h : Equation25532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X4)) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation25535_implies_Equation2 (G : Type*) [Magma G] (h : Equation25535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0)) ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq7 eq9
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X1) = (X0 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq7 eq10
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq14
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq147 eq51


@[equational_result]
theorem Equation25536_implies_Equation2 (G : Type*) [Magma G] (h : Equation25536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation25538_implies_Equation2 (G : Type*) [Magma G] (h : Equation25538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation25539_implies_Equation2 (G : Type*) [Magma G] (h : Equation25539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation25540_implies_Equation2 (G : Type*) [Magma G] (h : Equation25540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq11
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq153 eq54


@[equational_result]
theorem Equation25541_implies_Equation2 (G : Type*) [Magma G] (h : Equation25541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation25545_implies_Equation2 (G : Type*) [Magma G] (h : Equation25545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq11 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation25547_implies_Equation2 (G : Type*) [Magma G] (h : Equation25547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25548_implies_Equation2 (G : Type*) [Magma G] (h : Equation25548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25549_implies_Equation2 (G : Type*) [Magma G] (h : Equation25549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25551_implies_Equation2 (G : Type*) [Magma G] (h : Equation25551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation25552_implies_Equation2 (G : Type*) [Magma G] (h : Equation25552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25553_implies_Equation2 (G : Type*) [Magma G] (h : Equation25553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25555_implies_Equation2 (G : Type*) [Magma G] (h : Equation25555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25556_implies_Equation2 (G : Type*) [Magma G] (h : Equation25556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25557_implies_Equation2 (G : Type*) [Magma G] (h : Equation25557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25558_implies_Equation2 (G : Type*) [Magma G] (h : Equation25558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25561_implies_Equation2 (G : Type*) [Magma G] (h : Equation25561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X2))) = ((X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2)))) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq9 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X2 ◇ X2))) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq9 eq10
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X3 ◇ X2) := superpose eq9 eq12
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq9 eq11
  have eq20 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq17 eq13
  have eq21 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq20 eq17
  have eq26 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq20 eq21
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq20 eq26
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation25562_implies_Equation2 (G : Type*) [Magma G] (h : Equation25562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq11 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation25564_implies_Equation2 (G : Type*) [Magma G] (h : Equation25564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25565_implies_Equation2 (G : Type*) [Magma G] (h : Equation25565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25566_implies_Equation2 (G : Type*) [Magma G] (h : Equation25566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25568_implies_Equation2 (G : Type*) [Magma G] (h : Equation25568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25569_implies_Equation2 (G : Type*) [Magma G] (h : Equation25569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation25570_implies_Equation2 (G : Type*) [Magma G] (h : Equation25570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25572_implies_Equation2 (G : Type*) [Magma G] (h : Equation25572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25573_implies_Equation2 (G : Type*) [Magma G] (h : Equation25573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25574_implies_Equation2 (G : Type*) [Magma G] (h : Equation25574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25575_implies_Equation2 (G : Type*) [Magma G] (h : Equation25575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25577_implies_Equation2 (G : Type*) [Magma G] (h : Equation25577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) ◇ (X5 ◇ X3)) = X5 := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X6 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ (X4 ◇ X5)))))) = X6 := superpose eq10 eq10
  have eq29 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X6 ◇ (X6 ◇ X7))))) = X2 := superpose eq11 eq11
  have eq52 (X3 X4 X5 : G) : (X4 ◇ (X5 ◇ X3)) = X5 := superpose eq29 eq15
  have eq53 (X0 X1 X2 X6 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = X6 := superpose eq29 eq20
  have eq70 (X0 X1 X6 : G) : (X0 ◇ X1) = X6 := superpose eq52 eq53
  have eq71 (X0 X3 : G) : X0 = X3 := superpose eq70 eq70
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq79 eq71


@[equational_result]
theorem Equation25578_implies_Equation2 (G : Type*) [Magma G] (h : Equation25578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X3))) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq19 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X3))) = X1 := superpose eq14 eq13
  have eq21 (X1 X3 X4 : G) : ((X3 ◇ X1) ◇ (X4 ◇ X1)) = X4 := superpose eq19 eq10
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq11 eq21
  have eq29 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq21 eq21
  have eq31 (X2 X3 : G) : (X3 ◇ X2) = X2 := superpose eq28 eq29
  have eq32 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq31 eq11
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq32 eq32
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation25579_implies_Equation2 (G : Type*) [Magma G] (h : Equation25579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq11 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation25580_implies_Equation2 (G : Type*) [Magma G] (h : Equation25580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq11 eq18
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq42 eq29


@[equational_result]
theorem Equation25582_implies_Equation2 (G : Type*) [Magma G] (h : Equation25582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25583_implies_Equation2 (G : Type*) [Magma G] (h : Equation25583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25584_implies_Equation2 (G : Type*) [Magma G] (h : Equation25584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25585_implies_Equation2 (G : Type*) [Magma G] (h : Equation25585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25587_implies_Equation2 (G : Type*) [Magma G] (h : Equation25587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25588_implies_Equation2 (G : Type*) [Magma G] (h : Equation25588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25589_implies_Equation2 (G : Type*) [Magma G] (h : Equation25589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25590_implies_Equation2 (G : Type*) [Magma G] (h : Equation25590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25592_implies_Equation2 (G : Type*) [Magma G] (h : Equation25592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25593_implies_Equation2 (G : Type*) [Magma G] (h : Equation25593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25594_implies_Equation2 (G : Type*) [Magma G] (h : Equation25594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation25595_implies_Equation2 (G : Type*) [Magma G] (h : Equation25595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25597_implies_Equation2 (G : Type*) [Magma G] (h : Equation25597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25598_implies_Equation2 (G : Type*) [Magma G] (h : Equation25598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25599_implies_Equation2 (G : Type*) [Magma G] (h : Equation25599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25600_implies_Equation2 (G : Type*) [Magma G] (h : Equation25600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25601_implies_Equation2 (G : Type*) [Magma G] (h : Equation25601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25603_implies_Equation2 (G : Type*) [Magma G] (h : Equation25603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X4 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq10 eq10
  have eq21 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq14 eq11
  have eq25 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq21 eq14
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq10 eq25
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq45 eq31


@[equational_result]
theorem Equation25604_implies_Equation2 (G : Type*) [Magma G] (h : Equation25604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X0))) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ X0))) = X1 := superpose eq14 eq13
  have eq21 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X3)) = X3 := superpose eq19 eq10
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq21 eq14
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq72 eq30


@[equational_result]
theorem Equation25605_implies_Equation2 (G : Type*) [Magma G] (h : Equation25605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq60 eq27


@[equational_result]
theorem Equation25606_implies_Equation2 (G : Type*) [Magma G] (h : Equation25606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25608_implies_Equation2 (G : Type*) [Magma G] (h : Equation25608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation25609_implies_Equation2 (G : Type*) [Magma G] (h : Equation25609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq153 eq67


@[equational_result]
theorem Equation25610_implies_Equation2 (G : Type*) [Magma G] (h : Equation25610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation25611_implies_Equation2 (G : Type*) [Magma G] (h : Equation25611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X6)) = X5 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation25613_implies_Equation2 (G : Type*) [Magma G] (h : Equation25613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X3) = ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq154 eq67


@[equational_result]
theorem Equation25614_implies_Equation2 (G : Type*) [Magma G] (h : Equation25614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation25615_implies_Equation2 (G : Type*) [Magma G] (h : Equation25615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq55 eq16


@[equational_result]
theorem Equation25616_implies_Equation2 (G : Type*) [Magma G] (h : Equation25616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 X6 : G) : (X0 ◇ (X2 ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation25618_implies_Equation2 (G : Type*) [Magma G] (h : Equation25618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation25619_implies_Equation2 (G : Type*) [Magma G] (h : Equation25619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation25620_implies_Equation2 (G : Type*) [Magma G] (h : Equation25620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X3)) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation25621_implies_Equation2 (G : Type*) [Magma G] (h : Equation25621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25623_implies_Equation2 (G : Type*) [Magma G] (h : Equation25623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : ((X1 ◇ X0) ◇ (X6 ◇ X1)) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation25624_implies_Equation2 (G : Type*) [Magma G] (h : Equation25624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : (X0 ◇ (X6 ◇ X5)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq68 eq16


@[equational_result]
theorem Equation25625_implies_Equation2 (G : Type*) [Magma G] (h : Equation25625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X6 : G) : (X0 ◇ (X6 ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25626_implies_Equation2 (G : Type*) [Magma G] (h : Equation25626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X6 ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25627_implies_Equation2 (G : Type*) [Magma G] (h : Equation25627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X6 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation25629_implies_Equation2 (G : Type*) [Magma G] (h : Equation25629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X5 ◇ (X0 ◇ X1))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X5 : G) : (X2 ◇ (X5 ◇ (X0 ◇ X1))) = X5 := superpose eq10 eq9
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq7
  have eq14 (X0 X2 X5 : G) : (X2 ◇ X0) = X5 := superpose eq13 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation25630_implies_Equation2 (G : Type*) [Magma G] (h : Equation25630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X5 ◇ X2)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X2 ◇ (X5 ◇ X4))) = ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1))) ◇ X0) = ((X4 ◇ X5) ◇ (X2 ◇ X4)) := superpose eq9 eq7
  have eq23 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ (X5 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X6 ◇ X5))))) = X4 := superpose eq7 eq10
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq48 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1))) ◇ X0) = X2 := superpose eq32 eq21
  have eq53 (X2 X4 X5 : G) : (X4 ◇ (X2 ◇ (X5 ◇ X4))) = X2 := superpose eq48 eq11
  have eq58 (X0 X2 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X2 ◇ (X6 ◇ X5))))) = X4 := superpose eq53 eq23
  have eq63 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X4 := superpose eq53 eq58
  have eq65 (X2 X4 X5 : G) : (X4 ◇ X5) = X2 := superpose eq63 eq53
  have eq66 (X0 X3 : G) : X0 = X3 := superpose eq65 eq65
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq68 eq66


@[equational_result]
theorem Equation25631_implies_Equation2 (G : Type*) [Magma G] (h : Equation25631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X5 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X3))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X4 ◇ (X3 ◇ X1))) = X4 := superpose eq10 eq7
  have eq33 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq9
  have eq36 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X0) ◇ (X6 ◇ X5)) = (((X2 ◇ X3) ◇ (X4 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq44 (X0 X5 X6 : G) : ((X5 ◇ X0) ◇ (X6 ◇ X5)) = X0 := superpose eq33 eq36
  have eq49 (X1 X3 X4 : G) : (X1 ◇ (X4 ◇ (X3 ◇ X1))) = X4 := superpose eq44 eq18
  have eq56 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq49 eq7
  have eq63 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq56 eq12
  have eq67 (X0 X2 : G) : X0 = X2 := superpose eq10 eq63
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq85 eq67


@[equational_result]
theorem Equation25632_implies_Equation2 (G : Type*) [Magma G] (h : Equation25632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq7
  have eq10 (X0 X1 X5 X6 : G) : ((X1 ◇ X0) ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq13 (X2 X6 X7 : G) : (X2 ◇ (X6 ◇ X7)) = X6 := superpose eq10 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq13 eq17
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq61 eq28


@[equational_result]
theorem Equation25634_implies_Equation2 (G : Type*) [Magma G] (h : Equation25634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation25635_implies_Equation2 (G : Type*) [Magma G] (h : Equation25635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25636_implies_Equation2 (G : Type*) [Magma G] (h : Equation25636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation25637_implies_Equation2 (G : Type*) [Magma G] (h : Equation25637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation25639_implies_Equation2 (G : Type*) [Magma G] (h : Equation25639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


