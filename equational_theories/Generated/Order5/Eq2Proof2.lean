import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation6774_implies_Equation2 (G : Type*) [Magma G] (h : Equation6774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X5 ◇ (X0 ◇ ((X3 ◇ X3) ◇ (X4 ◇ X3))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq29 eq17


@[equational_result]
theorem Equation6775_implies_Equation2 (G : Type*) [Magma G] (h : Equation6775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation6776_implies_Equation2 (G : Type*) [Magma G] (h : Equation6776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X6 ◇ X7)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation6778_implies_Equation2 (G : Type*) [Magma G] (h : Equation6778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq9
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq11 eq18
  have eq61 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq44 eq16
  have eq76 (X0 X1 : G) : X0 = X1 := superpose eq18 eq61
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq81 eq76


@[equational_result]
theorem Equation6779_implies_Equation2 (G : Type*) [Magma G] (h : Equation6779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X3))) ◇ X5) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq13 eq10
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq18
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq38 eq20


@[equational_result]
theorem Equation6780_implies_Equation2 (G : Type*) [Magma G] (h : Equation6780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X5))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq12
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq39 eq15


@[equational_result]
theorem Equation6781_implies_Equation2 (G : Type*) [Magma G] (h : Equation6781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq21 (X1 X2 X3 X4 : G) : (X1 ◇ (X3 ◇ X4)) = X2 := superpose eq15 eq10
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq11 eq21
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq32 eq25


@[equational_result]
theorem Equation6783_implies_Equation2 (G : Type*) [Magma G] (h : Equation6783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq34 eq15


@[equational_result]
theorem Equation6784_implies_Equation2 (G : Type*) [Magma G] (h : Equation6784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq9
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation6785_implies_Equation2 (G : Type*) [Magma G] (h : Equation6785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X4 ◇ X5) ◇ (X3 ◇ X5))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3)))))) = X5 := superpose eq7 eq11
  have eq30 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))))) = X5 := superpose eq11 eq9
  have eq47 (X0 X5 : G) : (X0 ◇ X5) = X5 := superpose eq33 eq12
  have eq48 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq47 eq30
  have eq69 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq47 eq48
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq69 eq69
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq75 eq70


@[equational_result]
theorem Equation6786_implies_Equation2 (G : Type*) [Magma G] (h : Equation6786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq27 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq45 eq27


@[equational_result]
theorem Equation6788_implies_Equation2 (G : Type*) [Magma G] (h : Equation6788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq9
  have eq32 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq17 eq17
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq17 eq32
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq50 eq33


@[equational_result]
theorem Equation6789_implies_Equation2 (G : Type*) [Magma G] (h : Equation6789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation6790_implies_Equation2 (G : Type*) [Magma G] (h : Equation6790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation6791_implies_Equation2 (G : Type*) [Magma G] (h : Equation6791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X7)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation6793_implies_Equation2 (G : Type*) [Magma G] (h : Equation6793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq32 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq12 eq11
  have eq38 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X4 := superpose eq12 eq11
  have eq58 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq32 eq38
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq58 eq58
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq71 eq59


@[equational_result]
theorem Equation6794_implies_Equation2 (G : Type*) [Magma G] (h : Equation6794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq7
  have eq16 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq11 eq12
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation6795_implies_Equation2 (G : Type*) [Magma G] (h : Equation6795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ ((X4 ◇ X5) ◇ (X5 ◇ X5))) ◇ (X0 ◇ ((X4 ◇ X5) ◇ (X5 ◇ X5))))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X0 := superpose eq13 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6796_implies_Equation2 (G : Type*) [Magma G] (h : Equation6796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ ((X4 ◇ X5) ◇ (X5 ◇ X6))) ◇ X7)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation6798_implies_Equation2 (G : Type*) [Magma G] (h : Equation6798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq12 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq14
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq14 eq18
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq26 eq19


@[equational_result]
theorem Equation6799_implies_Equation2 (G : Type*) [Magma G] (h : Equation6799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X4 := superpose eq7 eq7
  have eq23 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq30 eq23


@[equational_result]
theorem Equation6800_implies_Equation2 (G : Type*) [Magma G] (h : Equation6800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X7 ◇ (X0 ◇ ((X4 ◇ X5) ◇ (X6 ◇ X5))))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq29 eq17


@[equational_result]
theorem Equation6801_implies_Equation2 (G : Type*) [Magma G] (h : Equation6801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation6802_implies_Equation2 (G : Type*) [Magma G] (h : Equation6802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X8 X9 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X8 ◇ X9)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation6805_implies_Equation2 (G : Type*) [Magma G] (h : Equation6805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq9
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation6808_implies_Equation2 (G : Type*) [Magma G] (h : Equation6808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq9
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq41 eq32


@[equational_result]
theorem Equation6810_implies_Equation2 (G : Type*) [Magma G] (h : Equation6810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) ◇ ((X3 ◇ X3) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq22 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq10 eq9
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq22
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq22 eq29
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq134 eq55


@[equational_result]
theorem Equation6811_implies_Equation2 (G : Type*) [Magma G] (h : Equation6811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq10 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq9
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq12 eq10
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq13 eq11
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6812_implies_Equation2 (G : Type*) [Magma G] (h : Equation6812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation6815_implies_Equation2 (G : Type*) [Magma G] (h : Equation6815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq10
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq103 eq38


@[equational_result]
theorem Equation6818_implies_Equation2 (G : Type*) [Magma G] (h : Equation6818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq10
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq98 eq35


@[equational_result]
theorem Equation6822_implies_Equation2 (G : Type*) [Magma G] (h : Equation6822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation6824_implies_Equation2 (G : Type*) [Magma G] (h : Equation6824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X3) ◇ X0))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X3) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X3) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X4) ◇ X1))) := superpose eq9 eq10
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) = ((((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X4) ◇ X0)) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X4) ◇ X0)) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))))) := superpose eq10 eq10
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X4) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X1))) ◇ ((X1 ◇ ((((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X4) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X1))) ◇ X0)) = X1 := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X4) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X4) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X0))) ◇ X0)) = X0 := superpose eq10 eq10
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq14
  have eq38 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq14
  have eq39 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))))) := superpose eq10 eq14
  have eq51 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X1))) ◇ ((X1 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X1))) ◇ X0)) = X1 := superpose eq37 eq26
  have eq53 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X0))) ◇ X0)) = X0 := superpose eq37 eq28
  have eq59 (X0 X1 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X4) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X4) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X5) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq37 eq22
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X1))) ◇ ((X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X1))) ◇ X0)) = X1 := superpose eq37 eq51
  have eq65 (X0 X1 X3 : G) : ((X0 ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ X0))) ◇ X0)) = X0 := superpose eq37 eq53
  have eq66 (X0 X1 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X4) ◇ X0)) ◇ ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X4) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq38 eq59
  have eq68 (X0 X1 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X4) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) := superpose eq38 eq66
  have eq69 (X0 X1 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) = ((((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X4) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq9 eq68
  have eq70 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq38 eq69
  have eq72 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X0)) = X0 := superpose eq70 eq65
  have eq73 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq14 eq72
  have eq75 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X3) ◇ X1) := superpose eq9 eq39
  have eq76 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X3) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X3) ◇ X0)) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1))) := superpose eq75 eq21
  have eq77 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ X2) ◇ X1))) ◇ ((X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0)) = X1 := superpose eq75 eq64
  have eq79 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq75 eq73
  have eq87 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X3) ◇ X0)) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1))) := superpose eq38 eq76
  have eq88 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X3) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1))) := superpose eq75 eq87
  have eq89 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ X3) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq75 eq88
  have eq90 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ ((X1 ◇ X3) ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq75 eq89
  have eq91 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq75 eq90
  have eq92 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ X2) ◇ X1))) ◇ (X1 ◇ X0)) = X1 := superpose eq75 eq77
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1))) ◇ (X1 ◇ X0)) = X1 := superpose eq38 eq92
  have eq94 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ (X1 ◇ X0)) = X1 := superpose eq75 eq93
  have eq95 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X0)) = X1 := superpose eq75 eq94
  have eq129 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq79
  have eq133 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq79 eq9
  have eq134 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq129 eq95
  have eq135 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq129 eq91
  have eq136 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := superpose eq75 eq135
  have eq138 (X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = X2 := superpose eq136 eq9
  have eq141 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq75 eq133
  have eq142 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq134 eq141
  have eq144 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq142 eq138
  have eq173 (X0 X2 : G) : X0 = X2 := superpose eq144 eq144
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq173 eq8
  subsumption eq175 eq173


@[equational_result]
theorem Equation6825_implies_Equation2 (G : Type*) [Magma G] (h : Equation6825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq34 eq15


@[equational_result]
theorem Equation6826_implies_Equation2 (G : Type*) [Magma G] (h : Equation6826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X2 := superpose eq7 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq38 eq30


@[equational_result]
theorem Equation6828_implies_Equation2 (G : Type*) [Magma G] (h : Equation6828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq23 eq13


@[equational_result]
theorem Equation6830_implies_Equation2 (G : Type*) [Magma G] (h : Equation6830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq12
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = X1 := superpose eq13 eq11
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq13 eq19
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation6834_implies_Equation2 (G : Type*) [Magma G] (h : Equation6834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X1 := superpose eq7 eq11
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq11
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq14 eq12
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq32 eq27


@[equational_result]
theorem Equation6836_implies_Equation2 (G : Type*) [Magma G] (h : Equation6836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X5 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation6837_implies_Equation2 (G : Type*) [Magma G] (h : Equation6837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation6838_implies_Equation2 (G : Type*) [Magma G] (h : Equation6838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X5 ◇ X5)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq7
  have eq13 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq10
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X5))) = X2 := superpose eq13 eq9
  have eq17 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq13 eq14
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq13 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation6839_implies_Equation2 (G : Type*) [Magma G] (h : Equation6839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq26 eq17


@[equational_result]
theorem Equation6842_implies_Equation2 (G : Type*) [Magma G] (h : Equation6842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq10
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq133 eq38


@[equational_result]
theorem Equation6845_implies_Equation2 (G : Type*) [Magma G] (h : Equation6845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq10
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq124 eq57


@[equational_result]
theorem Equation6847_implies_Equation2 (G : Type*) [Magma G] (h : Equation6847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ X3) ◇ X0))) = X3 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1))) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = X1 := superpose eq25 eq24
  have eq44 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ X0) ◇ X2)) = ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (X0 ◇ X2))) := superpose eq10 eq10
  have eq46 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X5 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))))) = ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))))) ◇ X1))) := superpose eq9 eq10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (X0 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))))) = ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ X0) ◇ X2)) ◇ (X5 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))))))) := superpose eq10 eq9
  have eq59 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)))) = X3 := superpose eq44 eq10
  have eq60 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X5 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))))) = ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))))) ◇ X1)))) := superpose eq44 eq46
  have eq66 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ X0) ◇ X2) = ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (X0 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))))) := superpose eq7 eq51
  have eq67 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))))) ◇ X1)))) := superpose eq66 eq60
  have eq111 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (X0 ◇ (X4 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))))) = ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (X0 ◇ X2)) := superpose eq59 eq25
  have eq122 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ X0) ◇ X2) = ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (X0 ◇ X2)) := superpose eq111 eq66
  have eq125 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (X3 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))))) ◇ X1)))) := superpose eq122 eq67
  have eq140 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq25 eq33
  have eq141 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) = (((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (X0 ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (X0 ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) ◇ (X0 ◇ X2)) ◇ X0))) := superpose eq59 eq33
  have eq156 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (X3 ◇ X1)) := superpose eq140 eq125
  have eq180 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) = (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X0))) := superpose eq156 eq141
  have eq181 (X1 X2 X3 : G) : (X3 ◇ X1) = (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) := superpose eq140 eq180
  have eq182 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq181 eq7
  have eq268 (X0 X3 : G) : X0 = X3 := superpose eq182 eq182
  have eq298 (X0 : G) : sK0 ≠ X0 := superpose eq268 eq8
  subsumption eq298 eq268


@[equational_result]
theorem Equation6848_implies_Equation2 (G : Type*) [Magma G] (h : Equation6848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X3)))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3)))) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X2)))) := superpose eq9 eq9
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := superpose eq9 eq9
  have eq18 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq7 eq9
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X2))))) := superpose eq9 eq7
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq9 eq18
  have eq37 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq18 eq7
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2)))) := superpose eq18 eq7
  have eq44 (X0 X2 X3 : G) : (X2 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) = (X2 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq35 eq16
  have eq50 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq41
  have eq53 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X2)))) = (X0 ◇ (X0 ◇ X1)) := superpose eq50 eq14
  have eq56 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq53 eq28
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq9 eq37
  have eq65 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := superpose eq57 eq53
  have eq67 (X0 X2 X3 : G) : (X2 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) = (X2 ◇ (X2 ◇ X0)) := superpose eq65 eq44
  have eq69 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq67 eq7
  have eq75 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq69 eq56
  have eq84 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq75 eq50
  have eq96 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq75 eq84
  have eq97 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq96 eq69
  have eq102 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq75 eq97
  have eq117 (X0 X2 : G) : X0 = X2 := superpose eq102 eq102
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq117 eq8
  subsumption eq119 eq117


@[equational_result]
theorem Equation6849_implies_Equation2 (G : Type*) [Magma G] (h : Equation6849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation6852_implies_Equation2 (G : Type*) [Magma G] (h : Equation6852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq11 eq7
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation6854_implies_Equation2 (G : Type*) [Magma G] (h : Equation6854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation6855_implies_Equation2 (G : Type*) [Magma G] (h : Equation6855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6857_implies_Equation2 (G : Type*) [Magma G] (h : Equation6857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6858_implies_Equation2 (G : Type*) [Magma G] (h : Equation6858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation6859_implies_Equation2 (G : Type*) [Magma G] (h : Equation6859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6861_implies_Equation2 (G : Type*) [Magma G] (h : Equation6861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ X3) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X0))) = X1 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq9 eq9
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) = ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ X4) ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ X4) ◇ X0)) ◇ (((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ X4) ◇ X0)) ◇ X5) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))))) := superpose eq10 eq10
  have eq32 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ X4) ◇ X3)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))))) := superpose eq10 eq14
  have eq35 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq14
  have eq46 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) = ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ X4) ◇ X0)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ X4) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))))) := superpose eq35 eq22
  have eq47 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ X4) ◇ X3)) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))))) := superpose eq35 eq32
  have eq48 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) = ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) ◇ X4) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))))) := superpose eq35 eq46
  have eq49 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))))) := superpose eq35 eq48
  have eq50 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq7 eq49
  have eq54 (X0 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ X4) ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))))) := superpose eq35 eq47
  have eq55 (X0 X2 X3 X4 : G) : (X0 ◇ X3) = ((X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) ◇ X4) ◇ X3)) := superpose eq7 eq54
  have eq56 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq55 eq50
  have eq59 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq56 eq35
  have eq62 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0))) = X1 := superpose eq59 eq11
  have eq66 (X0 X3 X4 : G) : (X0 ◇ X3) = ((X0 ◇ (X3 ◇ X0)) ◇ (((X0 ◇ (X3 ◇ X0)) ◇ X4) ◇ X3)) := superpose eq59 eq55
  have eq76 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X1 := superpose eq59 eq62
  have eq77 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X0)) = X1 := superpose eq59 eq76
  have eq80 (X0 X3 X4 : G) : (X0 ◇ X3) = ((X3 ◇ X0) ◇ (((X3 ◇ X0) ◇ X4) ◇ X3)) := superpose eq59 eq66
  have eq81 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq77 eq80
  have eq86 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X1 := superpose eq81 eq77
  have eq90 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq81 eq86
  have eq91 (X0 X3 : G) : X0 = X3 := superpose eq90 eq90
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq91 eq8
  subsumption eq93 eq91


@[equational_result]
theorem Equation6862_implies_Equation2 (G : Type*) [Magma G] (h : Equation6862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X1 := superpose eq9 eq9
  have eq18 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7 eq9
  have eq58 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq18 eq9
  have eq66 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq58
  have eq67 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq66 eq18
  have eq68 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq67 eq15
  have eq85 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq68 eq17
  have eq141 (X0 X2 : G) : X0 = X2 := superpose eq85 eq85
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq146 eq141


@[equational_result]
theorem Equation6863_implies_Equation2 (G : Type*) [Magma G] (h : Equation6863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq133 eq50


@[equational_result]
theorem Equation6865_implies_Equation2 (G : Type*) [Magma G] (h : Equation6865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6866_implies_Equation2 (G : Type*) [Magma G] (h : Equation6866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation6867_implies_Equation2 (G : Type*) [Magma G] (h : Equation6867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6869_implies_Equation2 (G : Type*) [Magma G] (h : Equation6869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6870_implies_Equation2 (G : Type*) [Magma G] (h : Equation6870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6871_implies_Equation2 (G : Type*) [Magma G] (h : Equation6871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6873_implies_Equation2 (G : Type*) [Magma G] (h : Equation6873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6874_implies_Equation2 (G : Type*) [Magma G] (h : Equation6874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6875_implies_Equation2 (G : Type*) [Magma G] (h : Equation6875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6876_implies_Equation2 (G : Type*) [Magma G] (h : Equation6876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6880_implies_Equation2 (G : Type*) [Magma G] (h : Equation6880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq10
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq48 eq31


@[equational_result]
theorem Equation6882_implies_Equation2 (G : Type*) [Magma G] (h : Equation6882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X4 ◇ (X4 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X4 ◇ X4)))) := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ (X4 ◇ X1)) ◇ (X2 ◇ X2))) = (X5 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := superpose eq9 eq9
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq9
  have eq25 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X4 ◇ (X2 ◇ X2)) := superpose eq17 eq10
  have eq27 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := superpose eq17 eq16
  have eq143 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := superpose eq25 eq7
  have eq160 (X0 X1 X5 : G) : (X5 ◇ X0) = X1 := superpose eq143 eq27
  have eq163 (X0 X3 : G) : X0 = X3 := superpose eq7 eq160
  have eq257 (X0 : G) : sK0 ≠ X0 := superpose eq163 eq8
  subsumption eq257 eq163


@[equational_result]
theorem Equation6884_implies_Equation2 (G : Type*) [Magma G] (h : Equation6884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X4))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X5)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) = X0 := superpose eq12 eq7
  have eq18 (X0 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X4))) = X0 := superpose eq17 eq9
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq18 eq7
  have eq21 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ X0))) = X3 := superpose eq20 eq10
  have eq27 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq20 eq21
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq20 eq27
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq34 eq29


@[equational_result]
theorem Equation6886_implies_Equation2 (G : Type*) [Magma G] (h : Equation6886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ X3) ◇ X0))) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = (X4 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X4)))) := superpose eq9 eq9
  have eq25 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X3))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1))) = X0 := superpose eq7 eq9
  have eq30 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ (X4 ◇ X2)) = (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ X3)))) := superpose eq9 eq7
  have eq35 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = X1 := superpose eq26 eq25
  have eq54 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1))) ◇ ((X4 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1)))) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1)))))) = (((X1 ◇ X0) ◇ X3) ◇ (((X1 ◇ X0) ◇ X3) ◇ X0)) := superpose eq10 eq9
  have eq65 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq26
  have eq98 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0))) = X1 := superpose eq7 eq35
  have eq136 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X2)) = X0 := superpose eq26 eq65
  have eq200 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X3)))) = ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2)))) := superpose eq65 eq18
  have eq201 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ ((X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ X1))) ◇ ((X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ X1))) ◇ X4)))) = (((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) := superpose eq10 eq18
  have eq294 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X4)) = ((X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) ◇ (X3 ◇ X4)) := superpose eq9 eq136
  have eq302 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ (X2 ◇ X2)) := superpose eq9 eq136
  have eq344 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ (((X1 ◇ X0) ◇ X3) ◇ X0)) = ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1)))))) := superpose eq294 eq54
  have eq345 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ (((X1 ◇ X0) ◇ X3) ◇ X0)) = ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1))) ◇ (X3 ◇ X3)) := superpose eq7 eq344
  have eq346 (X0 X1 X3 : G) : (X1 ◇ X3) = (((X1 ◇ X0) ◇ X3) ◇ (((X1 ◇ X0) ◇ X3) ◇ X0)) := superpose eq302 eq345
  have eq347 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X1))) = X1 := superpose eq346 eq98
  have eq348 (X1 X2 X3 X4 : G) : (X1 ◇ X2) = (X4 ◇ (X4 ◇ ((X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ X1))) ◇ ((X1 ◇ ((X3 ◇ X2) ◇ (X3 ◇ X1))) ◇ X4)))) := superpose eq346 eq201
  have eq355 (X1 X2 X4 : G) : (X1 ◇ X2) = (X4 ◇ X4) := superpose eq347 eq348
  have eq450 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X4) ◇ X3))) = X4 := superpose eq355 eq10
  have eq518 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X3)))) = X1 := superpose eq450 eq200
  have eq521 (X1 X2 X4 : G) : ((X4 ◇ X1) ◇ (X4 ◇ X2)) = X2 := superpose eq518 eq30
  have eq782 (X0 X2 : G) : X0 = X2 := superpose eq136 eq521
  have eq793 (X0 : G) : sK0 ≠ X0 := superpose eq782 eq8
  subsumption eq793 eq782


@[equational_result]
theorem Equation6888_implies_Equation2 (G : Type*) [Magma G] (h : Equation6888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq11 eq11
  have eq22 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq13 eq11
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation6890_implies_Equation2 (G : Type*) [Magma G] (h : Equation6890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X5 ◇ X1)))) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) = (((X5 ◇ X0) ◇ (X6 ◇ X3)) ◇ (((X5 ◇ X0) ◇ (X6 ◇ X3)) ◇ X0)) := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X3 ◇ ((X4 ◇ (X5 ◇ X1)) ◇ (X6 ◇ X3))) = (X7 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X4 ◇ X1))) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) = X5 := superpose eq9 eq7
  have eq41 (X0 X1 X2 X7 : G) : (X7 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = X1 := superpose eq29 eq28
  have eq48 (X1 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X1) = X5 := superpose eq41 eq34
  have eq49 (X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) = X3 := superpose eq48 eq25
  have eq59 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq49 eq7
  have eq68 (X0 X1 X7 : G) : (X7 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq59 eq41
  have eq83 (X0 X1 X7 : G) : (X7 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq59 eq68
  have eq84 (X0 X1 X7 : G) : (X7 ◇ (X1 ◇ X0)) = X1 := superpose eq59 eq83
  have eq85 (X0 X1 X7 : G) : (X7 ◇ X0) = X1 := superpose eq59 eq84
  have eq86 (X0 X3 : G) : X0 = X3 := superpose eq85 eq85
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq105 eq86


@[equational_result]
theorem Equation6891_implies_Equation2 (G : Type*) [Magma G] (h : Equation6891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ (X1 ◇ X0)) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation6892_implies_Equation2 (G : Type*) [Magma G] (h : Equation6892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq11
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq19 eq16


@[equational_result]
theorem Equation6893_implies_Equation2 (G : Type*) [Magma G] (h : Equation6893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq27 eq18


@[equational_result]
theorem Equation6897_implies_Equation2 (G : Type*) [Magma G] (h : Equation6897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) = X3 := superpose eq7 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq54 eq36


@[equational_result]
theorem Equation6899_implies_Equation2 (G : Type*) [Magma G] (h : Equation6899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6900_implies_Equation2 (G : Type*) [Magma G] (h : Equation6900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6901_implies_Equation2 (G : Type*) [Magma G] (h : Equation6901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6903_implies_Equation2 (G : Type*) [Magma G] (h : Equation6903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation6904_implies_Equation2 (G : Type*) [Magma G] (h : Equation6904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6905_implies_Equation2 (G : Type*) [Magma G] (h : Equation6905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6907_implies_Equation2 (G : Type*) [Magma G] (h : Equation6907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6908_implies_Equation2 (G : Type*) [Magma G] (h : Equation6908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6909_implies_Equation2 (G : Type*) [Magma G] (h : Equation6909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6910_implies_Equation2 (G : Type*) [Magma G] (h : Equation6910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6914_implies_Equation2 (G : Type*) [Magma G] (h : Equation6914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq125 eq51


@[equational_result]
theorem Equation6916_implies_Equation2 (G : Type*) [Magma G] (h : Equation6916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation6917_implies_Equation2 (G : Type*) [Magma G] (h : Equation6917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6918_implies_Equation2 (G : Type*) [Magma G] (h : Equation6918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6920_implies_Equation2 (G : Type*) [Magma G] (h : Equation6920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6921_implies_Equation2 (G : Type*) [Magma G] (h : Equation6921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation6922_implies_Equation2 (G : Type*) [Magma G] (h : Equation6922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6924_implies_Equation2 (G : Type*) [Magma G] (h : Equation6924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6925_implies_Equation2 (G : Type*) [Magma G] (h : Equation6925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6926_implies_Equation2 (G : Type*) [Magma G] (h : Equation6926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6927_implies_Equation2 (G : Type*) [Magma G] (h : Equation6927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6929_implies_Equation2 (G : Type*) [Magma G] (h : Equation6929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X5 ◇ X1)))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ ((X4 ◇ X5) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X0))) = X1 := superpose eq9 eq9
  have eq60 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X3)) = ((((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X3)) ◇ ((X6 ◇ X7) ◇ X0)) ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X3)) ◇ ((X6 ◇ X7) ◇ X0)) ◇ ((X8 ◇ X9) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))))) := superpose eq10 eq10
  have eq80 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq10
  have eq96 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X3)) = (((X6 ◇ X7) ◇ X0) ◇ (((X6 ◇ X7) ◇ X0) ◇ ((X8 ◇ X9) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))))) := superpose eq80 eq60
  have eq102 (X1 X5 : G) : (X1 ◇ (X1 ◇ (X5 ◇ X1))) = X5 := superpose eq80 eq9
  have eq104 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0))) = X1 := superpose eq80 eq13
  have eq132 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X3)) = (((X6 ◇ X7) ◇ X0) ◇ ((X8 ◇ X9) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))))) := superpose eq80 eq96
  have eq133 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X3)) = (((X6 ◇ X7) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))) := superpose eq80 eq132
  have eq134 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X3)) := superpose eq80 eq133
  have eq135 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X4 ◇ X5) ◇ X3)) := superpose eq80 eq134
  have eq136 (X0 X3 X4 X5 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ ((X4 ◇ X5) ◇ X3)) := superpose eq80 eq135
  have eq147 (X1 X5 : G) : (X1 ◇ (X5 ◇ X1)) = X5 := superpose eq80 eq102
  have eq149 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X1 := superpose eq80 eq104
  have eq150 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X0)) = X1 := superpose eq80 eq149
  have eq151 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq150 eq136
  have eq155 (X1 X5 : G) : (X1 ◇ X1) = X5 := superpose eq151 eq147
  have eq266 (X0 X2 : G) : X0 = X2 := superpose eq155 eq155
  have eq268 (X0 : G) : sK0 ≠ X0 := superpose eq266 eq8
  subsumption eq268 eq266


@[equational_result]
theorem Equation6930_implies_Equation2 (G : Type*) [Magma G] (h : Equation6930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X5 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq157 eq52


@[equational_result]
theorem Equation6931_implies_Equation2 (G : Type*) [Magma G] (h : Equation6931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X4))) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))))) ◇ X5) = X0 := superpose eq7 eq12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq12 eq12
  have eq56 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ (X0 ◇ X5)) ◇ X3))) = X0 := superpose eq7 eq11
  have eq79 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) = X0 := superpose eq7 eq22
  have eq125 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ X5) = X0 := superpose eq79 eq13
  have eq146 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X5))) = X0 := superpose eq125 eq56
  have eq161 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq125 eq146
  have eq162 (X0 X3 : G) : X0 = X3 := superpose eq161 eq161
  have eq180 (X0 : G) : sK0 ≠ X0 := superpose eq162 eq8
  subsumption eq180 eq162


@[equational_result]
theorem Equation6932_implies_Equation2 (G : Type*) [Magma G] (h : Equation6932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq63 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq133 eq63


@[equational_result]
theorem Equation6934_implies_Equation2 (G : Type*) [Magma G] (h : Equation6934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6935_implies_Equation2 (G : Type*) [Magma G] (h : Equation6935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6936_implies_Equation2 (G : Type*) [Magma G] (h : Equation6936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6937_implies_Equation2 (G : Type*) [Magma G] (h : Equation6937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6939_implies_Equation2 (G : Type*) [Magma G] (h : Equation6939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6940_implies_Equation2 (G : Type*) [Magma G] (h : Equation6940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6941_implies_Equation2 (G : Type*) [Magma G] (h : Equation6941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation6942_implies_Equation2 (G : Type*) [Magma G] (h : Equation6942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6944_implies_Equation2 (G : Type*) [Magma G] (h : Equation6944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6945_implies_Equation2 (G : Type*) [Magma G] (h : Equation6945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6946_implies_Equation2 (G : Type*) [Magma G] (h : Equation6946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation6947_implies_Equation2 (G : Type*) [Magma G] (h : Equation6947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6949_implies_Equation2 (G : Type*) [Magma G] (h : Equation6949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6950_implies_Equation2 (G : Type*) [Magma G] (h : Equation6950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6951_implies_Equation2 (G : Type*) [Magma G] (h : Equation6951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6952_implies_Equation2 (G : Type*) [Magma G] (h : Equation6952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation6953_implies_Equation2 (G : Type*) [Magma G] (h : Equation6953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation6955_implies_Equation2 (G : Type*) [Magma G] (h : Equation6955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ (X3 ◇ ((X2 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq7 eq11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)))) := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq12 eq14
  have eq17 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq16
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ ((X2 ◇ X2) ◇ X0))) = X2 := superpose eq17 eq9
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X3) = X2 := superpose eq17 eq18
  have eq23 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq17 eq22
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation6956_implies_Equation2 (G : Type*) [Magma G] (h : Equation6956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq12 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq45 eq28


@[equational_result]
theorem Equation6957_implies_Equation2 (G : Type*) [Magma G] (h : Equation6957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation6959_implies_Equation2 (G : Type*) [Magma G] (h : Equation6959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq42 eq12


@[equational_result]
theorem Equation6961_implies_Equation2 (G : Type*) [Magma G] (h : Equation6961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation6964_implies_Equation2 (G : Type*) [Magma G] (h : Equation6964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq11 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation6965_implies_Equation2 (G : Type*) [Magma G] (h : Equation6965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6967_implies_Equation2 (G : Type*) [Magma G] (h : Equation6967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq54 eq15


@[equational_result]
theorem Equation6968_implies_Equation2 (G : Type*) [Magma G] (h : Equation6968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation6969_implies_Equation2 (G : Type*) [Magma G] (h : Equation6969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6970_implies_Equation2 (G : Type*) [Magma G] (h : Equation6970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6972_implies_Equation2 (G : Type*) [Magma G] (h : Equation6972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq10
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X0))) = X2 := superpose eq11 eq9
  have eq18 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq11 eq15
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation6974_implies_Equation2 (G : Type*) [Magma G] (h : Equation6974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation6976_implies_Equation2 (G : Type*) [Magma G] (h : Equation6976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq37 eq12


@[equational_result]
theorem Equation6978_implies_Equation2 (G : Type*) [Magma G] (h : Equation6978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation6982_implies_Equation2 (G : Type*) [Magma G] (h : Equation6982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation6984_implies_Equation2 (G : Type*) [Magma G] (h : Equation6984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation6985_implies_Equation2 (G : Type*) [Magma G] (h : Equation6985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq51 eq13


@[equational_result]
theorem Equation6986_implies_Equation2 (G : Type*) [Magma G] (h : Equation6986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation6987_implies_Equation2 (G : Type*) [Magma G] (h : Equation6987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation6990_implies_Equation2 (G : Type*) [Magma G] (h : Equation6990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X0 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := superpose eq7 eq10
  have eq19 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X3 := superpose eq13 eq9
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq42 eq26


@[equational_result]
theorem Equation6991_implies_Equation2 (G : Type*) [Magma G] (h : Equation6991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation6995_implies_Equation2 (G : Type*) [Magma G] (h : Equation6995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation6998_implies_Equation2 (G : Type*) [Magma G] (h : Equation6998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0))) = X3 := superpose eq7 eq9
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq36 eq25


@[equational_result]
theorem Equation6999_implies_Equation2 (G : Type*) [Magma G] (h : Equation6999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation7001_implies_Equation2 (G : Type*) [Magma G] (h : Equation7001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation7002_implies_Equation2 (G : Type*) [Magma G] (h : Equation7002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq26 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq84 eq26


@[equational_result]
theorem Equation7003_implies_Equation2 (G : Type*) [Magma G] (h : Equation7003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3))) ◇ (X0 ◇ (X5 ◇ X5)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X5 ◇ X5)))) = X4 := superpose eq11 eq9
  have eq15 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq11 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7004_implies_Equation2 (G : Type*) [Magma G] (h : Equation7004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7006_implies_Equation2 (G : Type*) [Magma G] (h : Equation7006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : ((X1 ◇ X4) ◇ X1) = X0 := superpose eq7 eq12
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq124 eq52


@[equational_result]
theorem Equation7007_implies_Equation2 (G : Type*) [Magma G] (h : Equation7007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq7 eq12
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq118 eq49


@[equational_result]
theorem Equation7008_implies_Equation2 (G : Type*) [Magma G] (h : Equation7008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation7009_implies_Equation2 (G : Type*) [Magma G] (h : Equation7009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation7011_implies_Equation2 (G : Type*) [Magma G] (h : Equation7011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq50 eq13


@[equational_result]
theorem Equation7012_implies_Equation2 (G : Type*) [Magma G] (h : Equation7012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq56 eq19


@[equational_result]
theorem Equation7013_implies_Equation2 (G : Type*) [Magma G] (h : Equation7013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq53 eq15


@[equational_result]
theorem Equation7014_implies_Equation2 (G : Type*) [Magma G] (h : Equation7014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation7016_implies_Equation2 (G : Type*) [Magma G] (h : Equation7016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq53 eq22


@[equational_result]
theorem Equation7017_implies_Equation2 (G : Type*) [Magma G] (h : Equation7017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq11 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation7018_implies_Equation2 (G : Type*) [Magma G] (h : Equation7018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq58 eq17


@[equational_result]
theorem Equation7019_implies_Equation2 (G : Type*) [Magma G] (h : Equation7019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7021_implies_Equation2 (G : Type*) [Magma G] (h : Equation7021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation7022_implies_Equation2 (G : Type*) [Magma G] (h : Equation7022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation7023_implies_Equation2 (G : Type*) [Magma G] (h : Equation7023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation7024_implies_Equation2 (G : Type*) [Magma G] (h : Equation7024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X4 ◇ ((X0 ◇ X5) ◇ (X5 ◇ X6))) ◇ X7)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X1 X3 X4 : G) : (X1 ◇ X4) = X3 := superpose eq10 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation7026_implies_Equation2 (G : Type*) [Magma G] (h : Equation7026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation7027_implies_Equation2 (G : Type*) [Magma G] (h : Equation7027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation7028_implies_Equation2 (G : Type*) [Magma G] (h : Equation7028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation7029_implies_Equation2 (G : Type*) [Magma G] (h : Equation7029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7030_implies_Equation2 (G : Type*) [Magma G] (h : Equation7030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7032_implies_Equation2 (G : Type*) [Magma G] (h : Equation7032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ X1)))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) ◇ X2) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := superpose eq11 eq11
  have eq18 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq12 eq9
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq18
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq13 eq7
  have eq24 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq23 eq20
  have eq25 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq24 eq23
  have eq29 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq25 eq24
  have eq31 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq25 eq29
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation7034_implies_Equation2 (G : Type*) [Magma G] (h : Equation7034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation7036_implies_Equation2 (G : Type*) [Magma G] (h : Equation7036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation7038_implies_Equation2 (G : Type*) [Magma G] (h : Equation7038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation7042_implies_Equation2 (G : Type*) [Magma G] (h : Equation7042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation7044_implies_Equation2 (G : Type*) [Magma G] (h : Equation7044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq79 eq15


@[equational_result]
theorem Equation7045_implies_Equation2 (G : Type*) [Magma G] (h : Equation7045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq51 eq13


@[equational_result]
theorem Equation7046_implies_Equation2 (G : Type*) [Magma G] (h : Equation7046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation7047_implies_Equation2 (G : Type*) [Magma G] (h : Equation7047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7049_implies_Equation2 (G : Type*) [Magma G] (h : Equation7049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq10 eq7
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq103 eq48


@[equational_result]
theorem Equation7051_implies_Equation2 (G : Type*) [Magma G] (h : Equation7051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation7053_implies_Equation2 (G : Type*) [Magma G] (h : Equation7053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7054_implies_Equation2 (G : Type*) [Magma G] (h : Equation7054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7055_implies_Equation2 (G : Type*) [Magma G] (h : Equation7055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7057_implies_Equation2 (G : Type*) [Magma G] (h : Equation7057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7058_implies_Equation2 (G : Type*) [Magma G] (h : Equation7058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7059_implies_Equation2 (G : Type*) [Magma G] (h : Equation7059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7061_implies_Equation2 (G : Type*) [Magma G] (h : Equation7061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7062_implies_Equation2 (G : Type*) [Magma G] (h : Equation7062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7063_implies_Equation2 (G : Type*) [Magma G] (h : Equation7063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7064_implies_Equation2 (G : Type*) [Magma G] (h : Equation7064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7068_implies_Equation2 (G : Type*) [Magma G] (h : Equation7068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation7070_implies_Equation2 (G : Type*) [Magma G] (h : Equation7070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7071_implies_Equation2 (G : Type*) [Magma G] (h : Equation7071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7072_implies_Equation2 (G : Type*) [Magma G] (h : Equation7072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7074_implies_Equation2 (G : Type*) [Magma G] (h : Equation7074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7075_implies_Equation2 (G : Type*) [Magma G] (h : Equation7075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7076_implies_Equation2 (G : Type*) [Magma G] (h : Equation7076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7078_implies_Equation2 (G : Type*) [Magma G] (h : Equation7078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7079_implies_Equation2 (G : Type*) [Magma G] (h : Equation7079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7080_implies_Equation2 (G : Type*) [Magma G] (h : Equation7080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7081_implies_Equation2 (G : Type*) [Magma G] (h : Equation7081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7083_implies_Equation2 (G : Type*) [Magma G] (h : Equation7083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X4 : G) : ((X4 ◇ X1) ◇ X4) = X0 := superpose eq7 eq11
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq128 eq53


@[equational_result]
theorem Equation7084_implies_Equation2 (G : Type*) [Magma G] (h : Equation7084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X2))) ◇ ((X1 ◇ X5) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq12 eq11
  have eq14 (X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ X4) ◇ X2)) = X3 := superpose eq12 eq10
  have eq15 (X1 X4 : G) : (X1 ◇ X1) = X4 := superpose eq14 eq13
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq28 eq17


@[equational_result]
theorem Equation7085_implies_Equation2 (G : Type*) [Magma G] (h : Equation7085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq11
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq152 eq60


@[equational_result]
theorem Equation7086_implies_Equation2 (G : Type*) [Magma G] (h : Equation7086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation7088_implies_Equation2 (G : Type*) [Magma G] (h : Equation7088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7089_implies_Equation2 (G : Type*) [Magma G] (h : Equation7089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7090_implies_Equation2 (G : Type*) [Magma G] (h : Equation7090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7091_implies_Equation2 (G : Type*) [Magma G] (h : Equation7091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7093_implies_Equation2 (G : Type*) [Magma G] (h : Equation7093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7094_implies_Equation2 (G : Type*) [Magma G] (h : Equation7094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7095_implies_Equation2 (G : Type*) [Magma G] (h : Equation7095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7096_implies_Equation2 (G : Type*) [Magma G] (h : Equation7096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7098_implies_Equation2 (G : Type*) [Magma G] (h : Equation7098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7099_implies_Equation2 (G : Type*) [Magma G] (h : Equation7099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7100_implies_Equation2 (G : Type*) [Magma G] (h : Equation7100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7101_implies_Equation2 (G : Type*) [Magma G] (h : Equation7101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7103_implies_Equation2 (G : Type*) [Magma G] (h : Equation7103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7104_implies_Equation2 (G : Type*) [Magma G] (h : Equation7104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7105_implies_Equation2 (G : Type*) [Magma G] (h : Equation7105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7106_implies_Equation2 (G : Type*) [Magma G] (h : Equation7106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7107_implies_Equation2 (G : Type*) [Magma G] (h : Equation7107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7110_implies_Equation2 (G : Type*) [Magma G] (h : Equation7110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X3 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X3))) ◇ X2)) ◇ (X3 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X3))))) = X2 := superpose eq7 eq11
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq12
  have eq47 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq138 eq47


@[equational_result]
theorem Equation7111_implies_Equation2 (G : Type*) [Magma G] (h : Equation7111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation7115_implies_Equation2 (G : Type*) [Magma G] (h : Equation7115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation7118_implies_Equation2 (G : Type*) [Magma G] (h : Equation7118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) = (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ (X3 ◇ X3))) = (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ (X1 ◇ (X3 ◇ X3))) ◇ (((X3 ◇ (X1 ◇ (X3 ◇ X3))) ◇ X4) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))))) = X4 := superpose eq9 eq7
  have eq33 (X0 X1 X2 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) = X2 := superpose eq23 eq22
  have eq35 (X0 X1 X2 X4 : G) : (X2 ◇ (X0 ◇ X1)) = X4 := superpose eq33 eq29
  have eq62 (X0 X3 : G) : X0 = X3 := superpose eq7 eq35
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq174 eq62


@[equational_result]
theorem Equation7119_implies_Equation2 (G : Type*) [Magma G] (h : Equation7119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation7121_implies_Equation2 (G : Type*) [Magma G] (h : Equation7121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation7122_implies_Equation2 (G : Type*) [Magma G] (h : Equation7122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X2)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq82 eq24


@[equational_result]
theorem Equation7123_implies_Equation2 (G : Type*) [Magma G] (h : Equation7123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation7124_implies_Equation2 (G : Type*) [Magma G] (h : Equation7124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7128_implies_Equation2 (G : Type*) [Magma G] (h : Equation7128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq55 eq16


@[equational_result]
theorem Equation7130_implies_Equation2 (G : Type*) [Magma G] (h : Equation7130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7131_implies_Equation2 (G : Type*) [Magma G] (h : Equation7131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7132_implies_Equation2 (G : Type*) [Magma G] (h : Equation7132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7134_implies_Equation2 (G : Type*) [Magma G] (h : Equation7134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7135_implies_Equation2 (G : Type*) [Magma G] (h : Equation7135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7136_implies_Equation2 (G : Type*) [Magma G] (h : Equation7136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7138_implies_Equation2 (G : Type*) [Magma G] (h : Equation7138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7139_implies_Equation2 (G : Type*) [Magma G] (h : Equation7139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7140_implies_Equation2 (G : Type*) [Magma G] (h : Equation7140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7141_implies_Equation2 (G : Type*) [Magma G] (h : Equation7141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7144_implies_Equation2 (G : Type*) [Magma G] (h : Equation7144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X3 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X0 ◇ X0))) = X3 := superpose eq7 eq9
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq66 eq47


@[equational_result]
theorem Equation7145_implies_Equation2 (G : Type*) [Magma G] (h : Equation7145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation7147_implies_Equation2 (G : Type*) [Magma G] (h : Equation7147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7148_implies_Equation2 (G : Type*) [Magma G] (h : Equation7148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7149_implies_Equation2 (G : Type*) [Magma G] (h : Equation7149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7151_implies_Equation2 (G : Type*) [Magma G] (h : Equation7151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7152_implies_Equation2 (G : Type*) [Magma G] (h : Equation7152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7153_implies_Equation2 (G : Type*) [Magma G] (h : Equation7153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7155_implies_Equation2 (G : Type*) [Magma G] (h : Equation7155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7156_implies_Equation2 (G : Type*) [Magma G] (h : Equation7156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7157_implies_Equation2 (G : Type*) [Magma G] (h : Equation7157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7158_implies_Equation2 (G : Type*) [Magma G] (h : Equation7158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7160_implies_Equation2 (G : Type*) [Magma G] (h : Equation7160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X5 ◇ X1)))) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = X3 := superpose eq9 eq9
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq136 eq59


@[equational_result]
theorem Equation7161_implies_Equation2 (G : Type*) [Magma G] (h : Equation7161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X5 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq148 eq40


@[equational_result]
theorem Equation7162_implies_Equation2 (G : Type*) [Magma G] (h : Equation7162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq59 eq18


@[equational_result]
theorem Equation7163_implies_Equation2 (G : Type*) [Magma G] (h : Equation7163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation7165_implies_Equation2 (G : Type*) [Magma G] (h : Equation7165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7166_implies_Equation2 (G : Type*) [Magma G] (h : Equation7166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7167_implies_Equation2 (G : Type*) [Magma G] (h : Equation7167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7168_implies_Equation2 (G : Type*) [Magma G] (h : Equation7168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7170_implies_Equation2 (G : Type*) [Magma G] (h : Equation7170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7171_implies_Equation2 (G : Type*) [Magma G] (h : Equation7171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7172_implies_Equation2 (G : Type*) [Magma G] (h : Equation7172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7173_implies_Equation2 (G : Type*) [Magma G] (h : Equation7173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7175_implies_Equation2 (G : Type*) [Magma G] (h : Equation7175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7176_implies_Equation2 (G : Type*) [Magma G] (h : Equation7176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7177_implies_Equation2 (G : Type*) [Magma G] (h : Equation7177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7178_implies_Equation2 (G : Type*) [Magma G] (h : Equation7178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7180_implies_Equation2 (G : Type*) [Magma G] (h : Equation7180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7181_implies_Equation2 (G : Type*) [Magma G] (h : Equation7181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7182_implies_Equation2 (G : Type*) [Magma G] (h : Equation7182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7183_implies_Equation2 (G : Type*) [Magma G] (h : Equation7183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7184_implies_Equation2 (G : Type*) [Magma G] (h : Equation7184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7186_implies_Equation2 (G : Type*) [Magma G] (h : Equation7186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X4 ◇ X0)) = X3 := superpose eq7 eq7
  have eq52 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq11 eq7
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq52
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq157 eq57


@[equational_result]
theorem Equation7187_implies_Equation2 (G : Type*) [Magma G] (h : Equation7187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq29 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ ((X3 ◇ ((X4 ◇ X0) ◇ (X0 ◇ X3))) ◇ X5)) ◇ (X3 ◇ ((X4 ◇ X0) ◇ (X0 ◇ X3))))) = X5 := superpose eq7 eq11
  have eq52 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq29
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq52
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq148 eq53


@[equational_result]
theorem Equation7188_implies_Equation2 (G : Type*) [Magma G] (h : Equation7188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation7189_implies_Equation2 (G : Type*) [Magma G] (h : Equation7189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq54 eq17


@[equational_result]
theorem Equation7191_implies_Equation2 (G : Type*) [Magma G] (h : Equation7191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation7192_implies_Equation2 (G : Type*) [Magma G] (h : Equation7192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ X0) ◇ (X3 ◇ X4))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq46 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X3 ◇ ((X4 ◇ (X5 ◇ X2)) ◇ (X6 ◇ X3))) = (X7 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := superpose eq9 eq9
  have eq48 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X4 ◇ X1))) = X0 := superpose eq7 eq9
  have eq57 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ X2) ◇ ((X4 ◇ (X5 ◇ X6)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) = X6 := superpose eq9 eq7
  have eq69 (X0 X1 X2 X7 : G) : (X7 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = X2 := superpose eq48 eq46
  have eq75 (X2 X3 X6 : G) : ((X3 ◇ X2) ◇ X2) = X6 := superpose eq69 eq57
  have eq83 (X0 X3 : G) : X0 = X3 := superpose eq75 eq75
  have eq178 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq178 eq83


@[equational_result]
theorem Equation7193_implies_Equation2 (G : Type*) [Magma G] (h : Equation7193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq75 eq15


@[equational_result]
theorem Equation7194_implies_Equation2 (G : Type*) [Magma G] (h : Equation7194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation7196_implies_Equation2 (G : Type*) [Magma G] (h : Equation7196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X5) = X2 := superpose eq12 eq12
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ (X3 ◇ X1)) ◇ ((X4 ◇ X5) ◇ X0))) = X5 := superpose eq12 eq7
  have eq22 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq16 eq20
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq157 eq44


@[equational_result]
theorem Equation7197_implies_Equation2 (G : Type*) [Magma G] (h : Equation7197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X2))) ◇ ((X4 ◇ X5) ◇ X0))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X4 ◇ X5) ◇ X0))) = X5 := superpose eq11 eq10
  have eq16 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation7198_implies_Equation2 (G : Type*) [Magma G] (h : Equation7198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq75 eq15


@[equational_result]
theorem Equation7199_implies_Equation2 (G : Type*) [Magma G] (h : Equation7199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7201_implies_Equation2 (G : Type*) [Magma G] (h : Equation7201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation7202_implies_Equation2 (G : Type*) [Magma G] (h : Equation7202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq60 eq13


@[equational_result]
theorem Equation7203_implies_Equation2 (G : Type*) [Magma G] (h : Equation7203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7204_implies_Equation2 (G : Type*) [Magma G] (h : Equation7204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7206_implies_Equation2 (G : Type*) [Magma G] (h : Equation7206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation7207_implies_Equation2 (G : Type*) [Magma G] (h : Equation7207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation7208_implies_Equation2 (G : Type*) [Magma G] (h : Equation7208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7209_implies_Equation2 (G : Type*) [Magma G] (h : Equation7209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7210_implies_Equation2 (G : Type*) [Magma G] (h : Equation7210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7212_implies_Equation2 (G : Type*) [Magma G] (h : Equation7212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X3 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X0 ◇ X1)))) ◇ X4) = X0 := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X4)))) := superpose eq7 eq11
  have eq29 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = X0 := superpose eq15 eq12
  have eq33 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X0 := superpose eq29 eq7
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq33 eq33
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq50 eq40


@[equational_result]
theorem Equation7213_implies_Equation2 (G : Type*) [Magma G] (h : Equation7213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X2 ◇ X1))) = (X1 ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X1))) = X0 := superpose eq12 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq15 eq15
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq25 eq21


@[equational_result]
theorem Equation7214_implies_Equation2 (G : Type*) [Magma G] (h : Equation7214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq11
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq160 eq63


@[equational_result]
theorem Equation7215_implies_Equation2 (G : Type*) [Magma G] (h : Equation7215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation7217_implies_Equation2 (G : Type*) [Magma G] (h : Equation7217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7218_implies_Equation2 (G : Type*) [Magma G] (h : Equation7218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7219_implies_Equation2 (G : Type*) [Magma G] (h : Equation7219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7220_implies_Equation2 (G : Type*) [Magma G] (h : Equation7220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7222_implies_Equation2 (G : Type*) [Magma G] (h : Equation7222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7223_implies_Equation2 (G : Type*) [Magma G] (h : Equation7223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7224_implies_Equation2 (G : Type*) [Magma G] (h : Equation7224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7225_implies_Equation2 (G : Type*) [Magma G] (h : Equation7225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7227_implies_Equation2 (G : Type*) [Magma G] (h : Equation7227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7228_implies_Equation2 (G : Type*) [Magma G] (h : Equation7228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7229_implies_Equation2 (G : Type*) [Magma G] (h : Equation7229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7230_implies_Equation2 (G : Type*) [Magma G] (h : Equation7230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7232_implies_Equation2 (G : Type*) [Magma G] (h : Equation7232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7233_implies_Equation2 (G : Type*) [Magma G] (h : Equation7233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7234_implies_Equation2 (G : Type*) [Magma G] (h : Equation7234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7235_implies_Equation2 (G : Type*) [Magma G] (h : Equation7235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7236_implies_Equation2 (G : Type*) [Magma G] (h : Equation7236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7238_implies_Equation2 (G : Type*) [Magma G] (h : Equation7238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ (X4 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq52 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = X3 := superpose eq12 eq11
  have eq71 (X0 X3 : G) : X0 = X3 := superpose eq11 eq52
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq168 eq71


@[equational_result]
theorem Equation7239_implies_Equation2 (G : Type*) [Magma G] (h : Equation7239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X5 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X0 ◇ X0))) = X5 := superpose eq7 eq9
  have eq47 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq66 eq47


@[equational_result]
theorem Equation7240_implies_Equation2 (G : Type*) [Magma G] (h : Equation7240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq65 eq16


@[equational_result]
theorem Equation7241_implies_Equation2 (G : Type*) [Magma G] (h : Equation7241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation7243_implies_Equation2 (G : Type*) [Magma G] (h : Equation7243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7244_implies_Equation2 (G : Type*) [Magma G] (h : Equation7244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7245_implies_Equation2 (G : Type*) [Magma G] (h : Equation7245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7246_implies_Equation2 (G : Type*) [Magma G] (h : Equation7246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7248_implies_Equation2 (G : Type*) [Magma G] (h : Equation7248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7249_implies_Equation2 (G : Type*) [Magma G] (h : Equation7249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7250_implies_Equation2 (G : Type*) [Magma G] (h : Equation7250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7251_implies_Equation2 (G : Type*) [Magma G] (h : Equation7251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7253_implies_Equation2 (G : Type*) [Magma G] (h : Equation7253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7254_implies_Equation2 (G : Type*) [Magma G] (h : Equation7254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7255_implies_Equation2 (G : Type*) [Magma G] (h : Equation7255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7256_implies_Equation2 (G : Type*) [Magma G] (h : Equation7256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7258_implies_Equation2 (G : Type*) [Magma G] (h : Equation7258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7259_implies_Equation2 (G : Type*) [Magma G] (h : Equation7259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7260_implies_Equation2 (G : Type*) [Magma G] (h : Equation7260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7261_implies_Equation2 (G : Type*) [Magma G] (h : Equation7261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7262_implies_Equation2 (G : Type*) [Magma G] (h : Equation7262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7264_implies_Equation2 (G : Type*) [Magma G] (h : Equation7264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ X0)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ ((X4 ◇ X4) ◇ ((X0 ◇ X1) ◇ X0)))) = X2 := superpose eq11 eq7
  have eq20 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq11 eq7
  have eq24 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq20 eq18
  have eq25 (X0 X1 X3 X4 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X3 ◇ X0)) = X4 := superpose eq24 eq10
  have eq33 (X0 X1 X3 X4 : G) : (((X1 ◇ X1) ◇ X0) ◇ X3) = X4 := superpose eq24 eq25
  have eq34 (X1 X3 X4 : G) : ((X1 ◇ X1) ◇ X3) = X4 := superpose eq24 eq33
  have eq35 (X1 X3 X4 : G) : (X1 ◇ X3) = X4 := superpose eq24 eq34
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq35 eq35
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq38 eq36


@[equational_result]
theorem Equation7265_implies_Equation2 (G : Type*) [Magma G] (h : Equation7265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X3 ◇ X3) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq116 eq47


@[equational_result]
theorem Equation7266_implies_Equation2 (G : Type*) [Magma G] (h : Equation7266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq55 eq18


@[equational_result]
theorem Equation7267_implies_Equation2 (G : Type*) [Magma G] (h : Equation7267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation7269_implies_Equation2 (G : Type*) [Magma G] (h : Equation7269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7270_implies_Equation2 (G : Type*) [Magma G] (h : Equation7270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7271_implies_Equation2 (G : Type*) [Magma G] (h : Equation7271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7272_implies_Equation2 (G : Type*) [Magma G] (h : Equation7272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7274_implies_Equation2 (G : Type*) [Magma G] (h : Equation7274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7275_implies_Equation2 (G : Type*) [Magma G] (h : Equation7275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7276_implies_Equation2 (G : Type*) [Magma G] (h : Equation7276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7277_implies_Equation2 (G : Type*) [Magma G] (h : Equation7277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7279_implies_Equation2 (G : Type*) [Magma G] (h : Equation7279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7280_implies_Equation2 (G : Type*) [Magma G] (h : Equation7280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7281_implies_Equation2 (G : Type*) [Magma G] (h : Equation7281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7282_implies_Equation2 (G : Type*) [Magma G] (h : Equation7282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7284_implies_Equation2 (G : Type*) [Magma G] (h : Equation7284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7285_implies_Equation2 (G : Type*) [Magma G] (h : Equation7285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7286_implies_Equation2 (G : Type*) [Magma G] (h : Equation7286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7287_implies_Equation2 (G : Type*) [Magma G] (h : Equation7287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7288_implies_Equation2 (G : Type*) [Magma G] (h : Equation7288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7290_implies_Equation2 (G : Type*) [Magma G] (h : Equation7290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 X5 : G) : (X4 ◇ X5) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X5 ◇ X6) ◇ X5) = X0 := superpose eq7 eq12
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq153 eq55


@[equational_result]
theorem Equation7291_implies_Equation2 (G : Type*) [Magma G] (h : Equation7291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 X5 : G) : (X4 ◇ X5) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq119 eq49


@[equational_result]
theorem Equation7292_implies_Equation2 (G : Type*) [Magma G] (h : Equation7292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : (X1 ◇ (X2 ◇ X0)) = X6 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation7293_implies_Equation2 (G : Type*) [Magma G] (h : Equation7293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : (X1 ◇ (X2 ◇ X0)) = X6 := superpose eq7 eq7
  have eq18 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq55 eq18


@[equational_result]
theorem Equation7294_implies_Equation2 (G : Type*) [Magma G] (h : Equation7294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ X0)) = X5 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation7296_implies_Equation2 (G : Type*) [Magma G] (h : Equation7296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7297_implies_Equation2 (G : Type*) [Magma G] (h : Equation7297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7298_implies_Equation2 (G : Type*) [Magma G] (h : Equation7298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7299_implies_Equation2 (G : Type*) [Magma G] (h : Equation7299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7300_implies_Equation2 (G : Type*) [Magma G] (h : Equation7300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7302_implies_Equation2 (G : Type*) [Magma G] (h : Equation7302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7303_implies_Equation2 (G : Type*) [Magma G] (h : Equation7303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7304_implies_Equation2 (G : Type*) [Magma G] (h : Equation7304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7305_implies_Equation2 (G : Type*) [Magma G] (h : Equation7305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7306_implies_Equation2 (G : Type*) [Magma G] (h : Equation7306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7308_implies_Equation2 (G : Type*) [Magma G] (h : Equation7308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X3 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7309_implies_Equation2 (G : Type*) [Magma G] (h : Equation7309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X3 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7310_implies_Equation2 (G : Type*) [Magma G] (h : Equation7310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X3 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7311_implies_Equation2 (G : Type*) [Magma G] (h : Equation7311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X3 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7312_implies_Equation2 (G : Type*) [Magma G] (h : Equation7312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X3 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7314_implies_Equation2 (G : Type*) [Magma G] (h : Equation7314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X4 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7315_implies_Equation2 (G : Type*) [Magma G] (h : Equation7315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X4 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7316_implies_Equation2 (G : Type*) [Magma G] (h : Equation7316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X4 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7317_implies_Equation2 (G : Type*) [Magma G] (h : Equation7317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X4 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7318_implies_Equation2 (G : Type*) [Magma G] (h : Equation7318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X4 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7320_implies_Equation2 (G : Type*) [Magma G] (h : Equation7320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X5 ◇ X1)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7321_implies_Equation2 (G : Type*) [Magma G] (h : Equation7321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X5 ◇ X2)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7322_implies_Equation2 (G : Type*) [Magma G] (h : Equation7322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X5 ◇ X3)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7323_implies_Equation2 (G : Type*) [Magma G] (h : Equation7323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X5 ◇ X4)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7324_implies_Equation2 (G : Type*) [Magma G] (h : Equation7324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X5 ◇ X5)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7325_implies_Equation2 (G : Type*) [Magma G] (h : Equation7325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X5 ◇ X6)))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7531_implies_Equation2 (G : Type*) [Magma G] (h : Equation7531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation7534_implies_Equation2 (G : Type*) [Magma G] (h : Equation7534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq35 eq23


@[equational_result]
theorem Equation7536_implies_Equation2 (G : Type*) [Magma G] (h : Equation7536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq9
  have eq28 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9
  have eq36 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq16 eq9
  have eq68 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq36 eq10
  have eq125 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq9 eq21
  have eq155 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq125 eq28
  have eq159 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq155 eq21
  have eq185 (X0 X1 : G) : X0 = X1 := superpose eq68 eq159
  have eq199 (X0 : G) : sK0 ≠ X0 := superpose eq185 eq8
  subsumption eq199 eq185


@[equational_result]
theorem Equation7537_implies_Equation2 (G : Type*) [Magma G] (h : Equation7537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation7538_implies_Equation2 (G : Type*) [Magma G] (h : Equation7538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X4))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation7541_implies_Equation2 (G : Type*) [Magma G] (h : Equation7541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation7544_implies_Equation2 (G : Type*) [Magma G] (h : Equation7544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq9 eq12
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq20 eq13


@[equational_result]
theorem Equation7546_implies_Equation2 (G : Type*) [Magma G] (h : Equation7546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq9
  have eq22 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9
  have eq37 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq9 eq15
  have eq48 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq37 eq22
  have eq53 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq48 eq15
  have eq62 (X0 X1 : G) : X0 = X1 := superpose eq11 eq53
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq77 eq62


@[equational_result]
theorem Equation7547_implies_Equation2 (G : Type*) [Magma G] (h : Equation7547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation7548_implies_Equation2 (G : Type*) [Magma G] (h : Equation7548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X4))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq11 eq10
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7550_implies_Equation2 (G : Type*) [Magma G] (h : Equation7550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X2)))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) ◇ (X2 ◇ (X4 ◇ X2)))) ◇ X0) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ (((X0 ◇ X2) ◇ X0) ◇ X1))) := superpose eq10 eq7
  have eq31 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3))) = X0 := superpose eq7 eq20
  have eq76 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq31
  have eq91 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq31 eq31
  have eq159 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq31 eq76
  have eq186 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq159 eq91
  have eq191 (X0 X1 X2 X4 : G) : (((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) ◇ (X2 ◇ (X4 ◇ X2)))) ◇ X0) = X2 := superpose eq186 eq17
  have eq223 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) ◇ X0) = X2 := superpose eq186 eq191
  have eq224 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X2 := superpose eq186 eq223
  have eq225 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = X2 := superpose eq186 eq224
  have eq237 (X0 X3 : G) : X0 = X3 := superpose eq225 eq225
  have eq239 (X0 : G) : sK0 ≠ X0 := superpose eq237 eq8
  subsumption eq239 eq237


@[equational_result]
theorem Equation7551_implies_Equation2 (G : Type*) [Magma G] (h : Equation7551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq23 eq16


@[equational_result]
theorem Equation7552_implies_Equation2 (G : Type*) [Magma G] (h : Equation7552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation7554_implies_Equation2 (G : Type*) [Magma G] (h : Equation7554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) = X2 := superpose eq11 eq7
  have eq46 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X1) = X3 := superpose eq7 eq13
  have eq65 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq46 eq7
  have eq75 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq46 eq18
  have eq77 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq75 eq65
  have eq78 (X0 X3 : G) : X0 = X3 := superpose eq77 eq77
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq80 eq78


@[equational_result]
theorem Equation7556_implies_Equation2 (G : Type*) [Magma G] (h : Equation7556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation7558_implies_Equation2 (G : Type*) [Magma G] (h : Equation7558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X3)))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq9
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := superpose eq9 eq10
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) := superpose eq10 eq10
  have eq44 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq14 eq10
  have eq48 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) = X2 := superpose eq14 eq7
  have eq50 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))))) := superpose eq14 eq20
  have eq62 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq48
  have eq85 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq14 eq22
  have eq106 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq85 eq50
  have eq122 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq62
  have eq123 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq48 eq62
  have eq174 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ X0)) = X1 := superpose eq123 eq44
  have eq181 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq174 eq106
  have eq188 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq181 eq7
  have eq194 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq188 eq122
  have eq197 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq194 eq123
  have eq202 (X0 X3 : G) : X0 = X3 := superpose eq62 eq197
  have eq236 (X0 : G) : sK0 ≠ X0 := superpose eq202 eq8
  subsumption eq236 eq202


@[equational_result]
theorem Equation7559_implies_Equation2 (G : Type*) [Magma G] (h : Equation7559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq13
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq21 eq14


@[equational_result]
theorem Equation7560_implies_Equation2 (G : Type*) [Magma G] (h : Equation7560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation7562_implies_Equation2 (G : Type*) [Magma G] (h : Equation7562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq16 eq9
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq23 eq10
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation7563_implies_Equation2 (G : Type*) [Magma G] (h : Equation7563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation7564_implies_Equation2 (G : Type*) [Magma G] (h : Equation7564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation7565_implies_Equation2 (G : Type*) [Magma G] (h : Equation7565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X6))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7568_implies_Equation2 (G : Type*) [Magma G] (h : Equation7568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq9 eq10
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq19 eq14


@[equational_result]
theorem Equation7571_implies_Equation2 (G : Type*) [Magma G] (h : Equation7571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq10 eq11
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation7573_implies_Equation2 (G : Type*) [Magma G] (h : Equation7573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq9
  have eq27 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq14 eq9
  have eq32 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq14 eq9
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq27 eq32
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq17
  have eq40 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X1 := superpose eq9 eq17
  have eq52 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq40 eq33
  have eq54 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq52 eq34
  have eq72 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = X3 := superpose eq52 eq54
  have eq73 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq52 eq72
  have eq87 (X0 X1 : G) : X0 = X1 := superpose eq52 eq73
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq89 eq87


@[equational_result]
theorem Equation7574_implies_Equation2 (G : Type*) [Magma G] (h : Equation7574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)))) = X0 := superpose eq7 eq7
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq10
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))))) = X1 := superpose eq15 eq9
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq10 eq33
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq39 eq39
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq122 eq56


@[equational_result]
theorem Equation7575_implies_Equation2 (G : Type*) [Magma G] (h : Equation7575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X5))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X4))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq14
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation7578_implies_Equation2 (G : Type*) [Magma G] (h : Equation7578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq14
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation7581_implies_Equation2 (G : Type*) [Magma G] (h : Equation7581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq9 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq11
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7583_implies_Equation2 (G : Type*) [Magma G] (h : Equation7583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq10 eq7
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq10 eq9
  have eq25 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq9 eq10
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq22 eq15
  have eq29 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq28 eq9
  have eq33 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq28 eq9
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq29 eq33
  have eq42 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq25 eq41
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq42 eq9
  have eq56 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq42 eq45
  have eq61 (X0 X1 : G) : X0 = X1 := superpose eq56 eq42
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq63 eq61


@[equational_result]
theorem Equation7585_implies_Equation2 (G : Type*) [Magma G] (h : Equation7585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X4))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq11 eq10
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation7589_implies_Equation2 (G : Type*) [Magma G] (h : Equation7589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq11 eq12
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation7591_implies_Equation2 (G : Type*) [Magma G] (h : Equation7591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = ((((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ ((((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ (X3 ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)))))) := superpose eq7 eq10
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = ((((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)))) ◇ ((((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)))) ◇ (X3 ◇ (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))))))) := superpose eq10 eq10
  have eq14 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq10
  have eq18 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq14 eq12
  have eq19 (X0 X1 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))))) := superpose eq14 eq11
  have eq20 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq14 eq10
  have eq22 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq7
  have eq24 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq14 eq18
  have eq25 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq20 eq24
  have eq27 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq20 eq25
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq27 eq19
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq27 eq20
  have eq34 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq22 eq22
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq34 eq28
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq29 eq36
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq37 eq34
  have eq43 (X0 X2 : G) : X0 = X2 := superpose eq39 eq39
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq48 eq43


@[equational_result]
theorem Equation7593_implies_Equation2 (G : Type*) [Magma G] (h : Equation7593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq10 eq11
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation7597_implies_Equation2 (G : Type*) [Magma G] (h : Equation7597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq10 eq11
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation7599_implies_Equation2 (G : Type*) [Magma G] (h : Equation7599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq15 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq15 eq9
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq23 eq22
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation7600_implies_Equation2 (G : Type*) [Magma G] (h : Equation7600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq10
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation7601_implies_Equation2 (G : Type*) [Magma G] (h : Equation7601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X4)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq10
  have eq23 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq18 eq10
  have eq24 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq18 eq11
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq23 eq24
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq45 eq40


@[equational_result]
theorem Equation7602_implies_Equation2 (G : Type*) [Magma G] (h : Equation7602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X6))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7604_implies_Equation2 (G : Type*) [Magma G] (h : Equation7604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X3 ◇ X3)))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq7 eq9
  have eq15 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq9
  have eq19 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq7
  have eq22 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq9 eq10
  have eq31 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq19 eq19
  have eq44 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq22
  have eq55 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq31 eq44
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq55 eq14
  have eq63 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = X1 := superpose eq55 eq15
  have eq83 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq55 eq63
  have eq84 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq83 eq62
  have eq86 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq55 eq84
  have eq87 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq86 eq19
  have eq95 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq86 eq87
  have eq155 (X0 X1 : G) : X0 = X1 := superpose eq86 eq95
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq155 eq8
  subsumption eq160 eq155


@[equational_result]
theorem Equation7605_implies_Equation2 (G : Type*) [Magma G] (h : Equation7605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq10 eq13
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq21 eq14


@[equational_result]
theorem Equation7606_implies_Equation2 (G : Type*) [Magma G] (h : Equation7606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq14 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq10 eq11
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation7608_implies_Equation2 (G : Type*) [Magma G] (h : Equation7608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)))) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X4)) ◇ X4)) ◇ (X4 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X4)) ◇ X4))))) = X4 := superpose eq7 eq9
  have eq27 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0))) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq7 eq9
  have eq32 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq15 eq15
  have eq39 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq15 eq7
  have eq40 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq7 eq27
  have eq55 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X0) := superpose eq15 eq40
  have eq56 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq55
  have eq60 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq56 eq15
  have eq61 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq60 eq32
  have eq66 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq61 eq56
  have eq68 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0))) ◇ X0) := superpose eq66 eq27
  have eq71 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq66 eq39
  have eq75 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) ◇ X0) := superpose eq71 eq68
  have eq113 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ ((X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq75 eq75
  have eq141 (X0 X1 X2 : G) : ((X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose eq66 eq75
  have eq167 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq71 eq141
  have eq172 (X0 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X4)) ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X4))))) = X4 := superpose eq167 eq18
  have eq189 (X0 X2 X4 : G) : (((X0 ◇ X2) ◇ X4) ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X4)))) = X4 := superpose eq167 eq172
  have eq200 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq66 eq189
  have eq210 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq71 eq200
  have eq218 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X3 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) ◇ X0)) ◇ X1) = X0 := superpose eq210 eq113
  have eq231 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq210 eq218
  have eq245 (X0 X2 : G) : X0 = X2 := superpose eq231 eq231
  have eq253 (X0 : G) : sK0 ≠ X0 := superpose eq245 eq8
  subsumption eq253 eq245


@[equational_result]
theorem Equation7609_implies_Equation2 (G : Type*) [Magma G] (h : Equation7609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq10 eq7
  have eq98 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2))) ◇ X1) ◇ X0) = X3 := superpose eq7 eq14
  have eq99 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ X3) = (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) ◇ X0) := superpose eq10 eq14
  have eq100 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) ◇ X0) = X2 := superpose eq17 eq14
  have eq128 (X0 X2 X3 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ X3) = X2 := superpose eq100 eq99
  have eq147 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X3)) ◇ X1) ◇ X0) = X3 := superpose eq128 eq98
  have eq158 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq128 eq147
  have eq159 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq158 eq14
  have eq186 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X2 := superpose eq158 eq159
  have eq187 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq158 eq186
  have eq217 (X0 X1 : G) : X0 = X1 := superpose eq187 eq158
  have eq219 (X0 : G) : sK0 ≠ X0 := superpose eq217 eq8
  subsumption eq219 eq217


@[equational_result]
theorem Equation7610_implies_Equation2 (G : Type*) [Magma G] (h : Equation7610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq16 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq11 eq12
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq16 eq11
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation7612_implies_Equation2 (G : Type*) [Magma G] (h : Equation7612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X2)))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : (((X3 ◇ (((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) ◇ X3)) ◇ X2) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) ◇ (X4 ◇ (X2 ◇ X4)))) ◇ X0) = X2 := superpose eq7 eq10
  have eq47 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq9
  have eq53 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq47
  have eq57 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq47 eq47
  have eq58 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq47 eq11
  have eq60 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq47 eq7
  have eq73 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq60 eq47
  have eq75 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq73 eq58
  have eq119 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq60 eq75
  have eq125 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X3)))) = (((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X3)))) ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X3))))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq75
  have eq128 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq75 eq75
  have eq129 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq75 eq7
  have eq136 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq75 eq11
  have eq139 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0) := superpose eq75 eq7
  have eq153 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq128 eq57
  have eq171 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq119 eq139
  have eq172 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq128 eq171
  have eq173 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq172 eq47
  have eq174 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) ◇ X2) = X2 := superpose eq172 eq53
  have eq196 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X3)))) = ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq172 eq125
  have eq198 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq172 eq153
  have eq211 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq173 eq136
  have eq238 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq211 eq198
  have eq241 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ (X3 ◇ X0)) = X3 := superpose eq238 eq10
  have eq248 (X0 X2 X3 : G) : (((X3 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq238 eq20
  have eq256 (X0 X2 X3 X4 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X4 ◇ (X2 ◇ X4)))) ◇ X0) = X2 := superpose eq238 eq33
  have eq292 (X0 X2 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) = X2 := superpose eq238 eq174
  have eq300 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X3)))) = ((X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq238 eq196
  have eq324 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X0)) = X3 := superpose eq238 eq241
  have eq329 (X0 X2 : G) : ((((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq238 eq248
  have eq339 (X0 X2 X3 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X2)) ◇ X0) = X2 := superpose eq238 eq256
  have eq340 (X0 X2 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0) = X2 := superpose eq238 eq339
  have eq375 (X0 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq292 eq329
  have eq385 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq238 eq300
  have eq470 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq375 eq375
  have eq474 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq172 eq470
  have eq475 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose eq172 eq474
  have eq476 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq292 eq475
  have eq569 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq324 eq238
  have eq576 (X0 X2 : G) : (((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ X0) = X2 := superpose eq569 eq340
  have eq578 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq129 eq576
  have eq584 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq578 eq385
  have eq590 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq476 eq584
  have eq595 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq590 eq476
  have eq601 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq595 eq238
  have eq616 (X0 X1 : G) : X0 = X1 := superpose eq595 eq601
  have eq618 (X0 : G) : sK0 ≠ X0 := superpose eq616 eq8
  subsumption eq618 eq616


@[equational_result]
theorem Equation7613_implies_Equation2 (G : Type*) [Magma G] (h : Equation7613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation7614_implies_Equation2 (G : Type*) [Magma G] (h : Equation7614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X4))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation7616_implies_Equation2 (G : Type*) [Magma G] (h : Equation7616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X5)))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq10 eq10
  have eq37 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq16 eq9
  have eq67 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) = X2 := superpose eq11 eq11
  have eq72 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X5)) ◇ (X6 ◇ (X3 ◇ X7)))) ◇ X0) = X3 := superpose eq7 eq11
  have eq75 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X1 ◇ ((X5 ◇ (X1 ◇ X6)) ◇ (X7 ◇ (X0 ◇ X8)))) = (((X0 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X5 ◇ (X1 ◇ X6)) ◇ (X7 ◇ (X0 ◇ X8)))) ◇ X9)))) ◇ X0) := superpose eq11 eq11
  have eq80 (X0 X1 X2 X3 X4 X5 X6 : G) : (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ (X5 ◇ ((X0 ◇ X1) ◇ X6)))) := superpose eq11 eq9
  have eq85 (X0 X1 X5 X6 X7 X8 : G) : (X1 ◇ ((X5 ◇ (X1 ◇ X6)) ◇ (X7 ◇ (X0 ◇ X8)))) = (((X0 ◇ X1) ◇ (X1 ◇ ((X5 ◇ (X1 ◇ X6)) ◇ (X7 ◇ (X0 ◇ X8))))) ◇ X0) := superpose eq80 eq75
  have eq89 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X5)))) = ((X0 ◇ X1) ◇ X0) := superpose eq11 eq37
  have eq107 (X0 X1 X2 X3 : G) : (((X3 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) ◇ X3) ◇ X0) = X3 := superpose eq89 eq72
  have eq110 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X3 := superpose eq7 eq107
  have eq111 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X5)))) = X1 := superpose eq110 eq89
  have eq112 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq111 eq85
  have eq114 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq111 eq80
  have eq116 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) ◇ X2) = X2 := superpose eq114 eq67
  have eq118 (X0 X1 X3 X4 : G) : (((X3 ◇ (X0 ◇ X4)) ◇ X1) ◇ X0) = X1 := superpose eq114 eq12
  have eq138 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X2 := superpose eq114 eq116
  have eq139 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq138 eq112
  have eq154 (X0 X1 X3 X4 : G) : ((X3 ◇ (X0 ◇ X4)) ◇ X0) = X1 := superpose eq139 eq118
  have eq155 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq139 eq154
  have eq156 (X0 X3 : G) : X0 = X3 := superpose eq155 eq155
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq156 eq8
  subsumption eq158 eq156


@[equational_result]
theorem Equation7617_implies_Equation2 (G : Type*) [Magma G] (h : Equation7617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X2 := superpose eq11 eq9
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation7618_implies_Equation2 (G : Type*) [Magma G] (h : Equation7618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X4 ◇ (X0 ◇ X5)) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation7619_implies_Equation2 (G : Type*) [Magma G] (h : Equation7619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X7))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X6 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X6))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X2 := superpose eq11 eq9
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq14
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation7621_implies_Equation2 (G : Type*) [Magma G] (h : Equation7621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ ((X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X0) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X0 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2))))) := superpose eq7 eq10
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X2 ◇ X2)) ◇ (((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X2 ◇ X2))))) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = ((X2 ◇ X2) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) := superpose eq10 eq10
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1))) = X1 := superpose eq10 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2))) := superpose eq10 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ X2)) = (X2 ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ X2)) ◇ ((X4 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))) ◇ X2))) := superpose eq7 eq9
  have eq38 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))))) := superpose eq15 eq7
  have eq61 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq9 eq38
  have eq199 (X0 : G) : ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ (((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0))) := superpose eq14 eq17
  have eq323 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ X2)) = (X2 ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ X2)) ◇ (X0 ◇ X2))) := superpose eq7 eq18
  have eq516 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq323 eq7
  have eq625 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose eq516 eq7
  have eq635 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq7 eq625
  have eq636 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq635 eq61
  have eq703 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq635 eq323
  have eq705 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq635 eq9
  have eq713 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq635 eq15
  have eq714 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq635 eq7
  have eq774 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq705 eq635
  have eq775 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq705 eq636
  have eq849 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq703 eq7
  have eq850 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq703 eq9
  have eq877 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq713 eq849
  have eq939 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq877 eq774
  have eq960 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq713 eq850
  have eq1115 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq939 eq9
  have eq1116 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq939 eq10
  have eq1117 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))))) := superpose eq939 eq11
  have eq1140 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq877 eq1115
  have eq1141 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq877 eq1116
  have eq1142 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq877 eq1117
  have eq1624 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq939 eq705
  have eq1641 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq877 eq1624
  have eq1642 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq1641 eq705
  have eq1656 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq1641 eq775
  have eq2482 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq1140 eq960
  have eq2484 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq2482 eq1656
  have eq2485 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq877 eq2484
  have eq2488 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq2485 eq714
  have eq2632 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq1141 eq2488
  have eq2644 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq2632 eq199
  have eq2800 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq2632 eq2644
  have eq2801 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq2485 eq2800
  have eq2802 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq2632 eq2801
  have eq2803 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0)) := superpose eq2802 eq10
  have eq2804 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) ◇ (((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2)))) := superpose eq2802 eq12
  have eq2806 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = (X2 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2))) := superpose eq2802 eq17
  have eq2898 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq2802 eq1142
  have eq3015 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq2802 eq1642
  have eq3630 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) ◇ (((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2))) := superpose eq2802 eq2804
  have eq3784 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq2802 eq2898
  have eq3785 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq2802 eq3784
  have eq3952 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq2802 eq3015
  have eq3955 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq3952 eq3785
  have eq4186 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0)))) = X0 := superpose eq3955 eq7
  have eq4453 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2)) = X2 := superpose eq2806 eq4186
  have eq4524 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) ◇ X2) := superpose eq4453 eq3630
  have eq4529 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) = X2 := superpose eq3955 eq4524
  have eq4530 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = (X2 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) ◇ X2)) := superpose eq4529 eq2806
  have eq4600 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) := superpose eq3955 eq4530
  have eq4601 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = X2 := superpose eq2802 eq4600
  have eq4604 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = (X0 ◇ X0) := superpose eq4601 eq2803
  have eq4611 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X0 := superpose eq2802 eq4604
  have eq4612 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq4611 eq7
  have eq4682 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq2802 eq4612
  have eq4705 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq4682 eq4611
  have eq4742 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq4682 eq4705
  have eq5108 (X0 X1 : G) : X0 = X1 := superpose eq4682 eq4742
  have eq5110 (X0 : G) : sK0 ≠ X0 := superpose eq5108 eq8
  subsumption eq5110 eq5108


@[equational_result]
theorem Equation7623_implies_Equation2 (G : Type*) [Magma G] (h : Equation7623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq16 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq11 eq12
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation7625_implies_Equation2 (G : Type*) [Magma G] (h : Equation7625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) ◇ (X2 ◇ (((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)))))) = X2 := superpose eq9 eq9
  have eq13 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X1 := superpose eq7 eq9
  have eq16 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X2 := superpose eq13 eq12
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X0 ◇ X2)) = X2 := superpose eq13 eq10
  have eq23 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq18 eq18
  have eq29 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq23 eq16
  have eq50 (X0 X1 : G) : X0 = X1 := superpose eq23 eq29
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq76 eq50


@[equational_result]
theorem Equation7627_implies_Equation2 (G : Type*) [Magma G] (h : Equation7627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq10 eq11
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation7631_implies_Equation2 (G : Type*) [Magma G] (h : Equation7631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq10 eq11
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation7633_implies_Equation2 (G : Type*) [Magma G] (h : Equation7633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4))) = X2 := superpose eq7 eq7
  have eq54 (X0 X2 : G) : X0 = X2 := superpose eq9 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq66 eq54


@[equational_result]
theorem Equation7634_implies_Equation2 (G : Type*) [Magma G] (h : Equation7634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ X4))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq19 (X0 X1 X3 X4 : G) : (X3 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X4))) = X1 := superpose eq12 eq11
  have eq23 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq12 eq19
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation7635_implies_Equation2 (G : Type*) [Magma G] (h : Equation7635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X4)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)))) = X3 := superpose eq7 eq7
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq10 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq45 eq35


@[equational_result]
theorem Equation7636_implies_Equation2 (G : Type*) [Magma G] (h : Equation7636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X6))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq11 eq10
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7638_implies_Equation2 (G : Type*) [Magma G] (h : Equation7638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = (X1 ◇ ((X0 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) ◇ ((X3 ◇ X0) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X0) = (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X3)))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X4)))) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)))) = X4 := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) = X3 := superpose eq7 eq11
  have eq19 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)))) ◇ (X4 ◇ (X4 ◇ X2)))) ◇ X0) = X2 := superpose eq7 eq11
  have eq22 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq11 eq12
  have eq27 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq7 eq12
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = (X2 ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2))) := superpose eq7 eq10
  have eq72 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))))) = ((X3 ◇ (X3 ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))))) ◇ X0)) := superpose eq12 eq9
  have eq117 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X3)))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X3))) = (((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X2 ◇ (X2 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X3)))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X3)))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X3))) := superpose eq10 eq27
  have eq183 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X1)))))) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X1)))))))))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq15
  have eq185 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) = ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X2 ◇ (X3 ◇ (X3 ◇ ((X4 ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))))))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) := superpose eq27 eq15
  have eq378 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (((((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) ◇ (X3 ◇ (X3 ◇ X0)))) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq7 eq22
  have eq406 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq19 eq378
  have eq428 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X2))) = X1 := superpose eq406 eq7
  have eq438 (X0 X1 X2 X3 : G) : ((((X2 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X3 ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) = X1 := superpose eq406 eq15
  have eq1117 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X3 ◇ X2)))) ◇ X0) = X2 := superpose eq7 eq13
  have eq1183 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((((X2 ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X0)) ◇ ((X0 ◇ X2) ◇ (X4 ◇ (X4 ◇ X0)))) ◇ X0) ◇ X1))) = X2 := superpose eq1117 eq7
  have eq1352 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq1117 eq1183
  have eq1514 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq1352
  have eq1515 (X0 X1 : G) : ((((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq428 eq1352
  have eq1519 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq10 eq1352
  have eq1521 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq36 eq1352
  have eq1646 (X0 X1 X2 X3 : G) : ((((X2 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) = X1 := superpose eq1519 eq438
  have eq1659 (X0 X1 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq1519 eq1515
  have eq1662 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1514 eq1659
  have eq1666 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := superpose eq1646 eq1521
  have eq1684 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ X0) := superpose eq1666 eq406
  have eq1774 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq1662 eq1684
  have eq1795 (X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ (X1 ◇ (X1 ◇ X3))) = (((X3 ◇ X1) ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ (X1 ◇ (X1 ◇ X3)))) ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq1774 eq117
  have eq1822 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X1)))))) = ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X1)))))))))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq1774 eq183
  have eq1824 (X0 X2 X3 X4 : G) : ((X4 ◇ (X4 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) = ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ ((X4 ◇ (X4 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)))))) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) := superpose eq1774 eq185
  have eq2068 (X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = (((X3 ◇ X1) ◇ (X1 ◇ (X1 ◇ X3))) ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq1774 eq1795
  have eq2118 (X2 X3 X4 : G) : ((X4 ◇ (X4 ◇ X2)) ◇ X2) = ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ ((X4 ◇ (X4 ◇ X2)) ◇ X2))))) ◇ X2) := superpose eq1774 eq1824
  have eq2119 (X2 X3 : G) : ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ X2) = X2 := superpose eq1774 eq2118
  have eq2120 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq1352 eq2119
  have eq2126 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))))) := superpose eq2120 eq72
  have eq2137 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))))) = X0 := superpose eq1774 eq2126
  have eq2139 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq2137 eq1822
  have eq2141 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq1352 eq2139
  have eq2144 (X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = (X3 ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq2141 eq2068
  have eq2157 (X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = X1 := superpose eq1352 eq2144
  have eq2158 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq2157 eq7
  have eq2575 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq2157 eq1352
  have eq2712 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq2575 eq2158
  have eq2720 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq2575 eq2712
  have eq2723 (X0 X2 : G) : X0 = X2 := superpose eq2720 eq2720
  have eq2725 (X0 : G) : sK0 ≠ X0 := superpose eq2723 eq8
  subsumption eq2725 eq2723


@[equational_result]
theorem Equation7639_implies_Equation2 (G : Type*) [Magma G] (h : Equation7639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7640_implies_Equation2 (G : Type*) [Magma G] (h : Equation7640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7644_implies_Equation2 (G : Type*) [Magma G] (h : Equation7644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X1))) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation7647_implies_Equation2 (G : Type*) [Magma G] (h : Equation7647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X2))) = X0 := superpose eq13 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq14
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7648_implies_Equation2 (G : Type*) [Magma G] (h : Equation7648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X2))) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7650_implies_Equation2 (G : Type*) [Magma G] (h : Equation7650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq16 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq16 eq9
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq25 eq24
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation7651_implies_Equation2 (G : Type*) [Magma G] (h : Equation7651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7652_implies_Equation2 (G : Type*) [Magma G] (h : Equation7652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X4 ◇ (X4 ◇ X5)) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X3))) = X0 := superpose eq13 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq14
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7653_implies_Equation2 (G : Type*) [Magma G] (h : Equation7653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X6))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7655_implies_Equation2 (G : Type*) [Magma G] (h : Equation7655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X4 ◇ X5)))) ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X1)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1)) := superpose eq7 eq11
  have eq27 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq11 eq7
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq27
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq27 eq27
  have eq79 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X1)) = ((X1 ◇ X0) ◇ (X3 ◇ X1)) := superpose eq55 eq22
  have eq103 (X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X1)) = X3 := superpose eq52 eq79
  have eq106 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq103 eq27
  have eq114 (X0 X3 : G) : X0 = X3 := superpose eq106 eq106
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq114 eq8
  subsumption eq116 eq114


@[equational_result]
theorem Equation7656_implies_Equation2 (G : Type*) [Magma G] (h : Equation7656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq23 eq16


@[equational_result]
theorem Equation7657_implies_Equation2 (G : Type*) [Magma G] (h : Equation7657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq23 eq16


@[equational_result]
theorem Equation7658_implies_Equation2 (G : Type*) [Magma G] (h : Equation7658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq16 (X1 X2 X3 : G) : (X3 ◇ X1) = X2 := superpose eq11 eq12
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation7660_implies_Equation2 (G : Type*) [Magma G] (h : Equation7660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X4)) ◇ X4) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)))) = X4 := superpose eq7 eq7
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq10 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq47 eq35


@[equational_result]
theorem Equation7661_implies_Equation2 (G : Type*) [Magma G] (h : Equation7661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ X4))) = X2 := superpose eq7 eq7
  have eq30 (X0 X1 X2 X5 X6 : G) : (X5 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ (X6 ◇ X1))) := superpose eq11 eq11
  have eq31 (X0 X1 X2 X5 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X5 ◇ X2))) = X1 := superpose eq10 eq11
  have eq47 (X2 X5 : G) : (X5 ◇ X2) = X2 := superpose eq31 eq30
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq47 eq7
  have eq69 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq47 eq49
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq69 eq69
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq72 eq70


@[equational_result]
theorem Equation7662_implies_Equation2 (G : Type*) [Magma G] (h : Equation7662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X4 ◇ (X0 ◇ X0))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4))) = X3 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq7
  have eq28 (X0 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X4))) = X3 := superpose eq20 eq11
  have eq35 (X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X2)) = X3 := superpose eq20 eq28
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq35 eq35
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation7663_implies_Equation2 (G : Type*) [Magma G] (h : Equation7663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq16 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq11 eq12
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation7665_implies_Equation2 (G : Type*) [Magma G] (h : Equation7665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X2)) ◇ X4) ◇ (X0 ◇ (X1 ◇ X0))) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X4 ◇ (X5 ◇ X4))) = X3 := superpose eq11 eq11
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = X2 := superpose eq7 eq11
  have eq26 (X0 X1 X2 X5 : G) : ((X0 ◇ (X2 ◇ X1)) ◇ (X5 ◇ X0)) = X5 := superpose eq14 eq10
  have eq29 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq20 eq7
  have eq38 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq29 eq20
  have eq42 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ (X5 ◇ X0)) = X5 := superpose eq38 eq26
  have eq46 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ X0) = X5 := superpose eq38 eq42
  have eq47 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq38 eq46
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq47 eq47
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq50 eq48


@[equational_result]
theorem Equation7666_implies_Equation2 (G : Type*) [Magma G] (h : Equation7666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq15 (X2 X3 X4 : G) : (X3 ◇ X2) = X4 := superpose eq13 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7667_implies_Equation2 (G : Type*) [Magma G] (h : Equation7667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7668_implies_Equation2 (G : Type*) [Magma G] (h : Equation7668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X6))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7670_implies_Equation2 (G : Type*) [Magma G] (h : Equation7670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X3)) ◇ X4) ◇ (X0 ◇ (X1 ◇ X1))) = X4 := superpose eq7 eq7
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq9 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq69 eq35


@[equational_result]
theorem Equation7671_implies_Equation2 (G : Type*) [Magma G] (h : Equation7671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X2 := superpose eq11 eq9
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation7672_implies_Equation2 (G : Type*) [Magma G] (h : Equation7672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X4 ◇ (X5 ◇ X5)) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq15 (X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2)) = X4 := superpose eq13 eq12
  have eq16 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X2)) = X4 := superpose eq13 eq15
  have eq21 (X0 X2 : G) : X0 = X2 := superpose eq13 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq28 eq21


@[equational_result]
theorem Equation7673_implies_Equation2 (G : Type*) [Magma G] (h : Equation7673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X2 := superpose eq11 eq9
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq26 eq19


@[equational_result]
theorem Equation7675_implies_Equation2 (G : Type*) [Magma G] (h : Equation7675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq16 eq9
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq21 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation7676_implies_Equation2 (G : Type*) [Magma G] (h : Equation7676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7677_implies_Equation2 (G : Type*) [Magma G] (h : Equation7677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7678_implies_Equation2 (G : Type*) [Magma G] (h : Equation7678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X5 ◇ (X6 ◇ X7)) ◇ X7))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)))) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq15 (X1 X5 X6 : G) : (X5 ◇ X1) = X6 := superpose eq13 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7679_implies_Equation2 (G : Type*) [Magma G] (h : Equation7679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X8 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X8))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation7682_implies_Equation2 (G : Type*) [Magma G] (h : Equation7682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation7685_implies_Equation2 (G : Type*) [Magma G] (h : Equation7685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation7687_implies_Equation2 (G : Type*) [Magma G] (h : Equation7687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation7688_implies_Equation2 (G : Type*) [Magma G] (h : Equation7688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq51 eq13


@[equational_result]
theorem Equation7689_implies_Equation2 (G : Type*) [Magma G] (h : Equation7689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq34 eq16


@[equational_result]
theorem Equation7692_implies_Equation2 (G : Type*) [Magma G] (h : Equation7692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation7695_implies_Equation2 (G : Type*) [Magma G] (h : Equation7695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation7697_implies_Equation2 (G : Type*) [Magma G] (h : Equation7697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq28 eq13


@[equational_result]
theorem Equation7699_implies_Equation2 (G : Type*) [Magma G] (h : Equation7699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq44 eq15


@[equational_result]
theorem Equation7703_implies_Equation2 (G : Type*) [Magma G] (h : Equation7703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq30 eq18


@[equational_result]
theorem Equation7705_implies_Equation2 (G : Type*) [Magma G] (h : Equation7705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1))))) = X3 := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) ◇ X0)) = X1 := superpose eq7 eq9
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq26 eq7
  have eq53 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = X1 := superpose eq44 eq26
  have eq62 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq53
  have eq72 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq62 eq7
  have eq126 (X0 X2 : G) : X0 = X2 := superpose eq72 eq72
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq126 eq8
  subsumption eq135 eq126


@[equational_result]
theorem Equation7707_implies_Equation2 (G : Type*) [Magma G] (h : Equation7707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation7711_implies_Equation2 (G : Type*) [Magma G] (h : Equation7711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation7713_implies_Equation2 (G : Type*) [Magma G] (h : Equation7713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation7714_implies_Equation2 (G : Type*) [Magma G] (h : Equation7714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq37 eq16


@[equational_result]
theorem Equation7715_implies_Equation2 (G : Type*) [Magma G] (h : Equation7715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X4)))) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq55 eq22


@[equational_result]
theorem Equation7716_implies_Equation2 (G : Type*) [Magma G] (h : Equation7716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq34 eq16


@[equational_result]
theorem Equation7719_implies_Equation2 (G : Type*) [Magma G] (h : Equation7719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation7722_implies_Equation2 (G : Type*) [Magma G] (h : Equation7722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq48 eq14


@[equational_result]
theorem Equation7724_implies_Equation2 (G : Type*) [Magma G] (h : Equation7724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq40 eq13


@[equational_result]
theorem Equation7725_implies_Equation2 (G : Type*) [Magma G] (h : Equation7725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))))) = X1 := superpose eq7 eq10
  have eq18 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq10 eq13
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq7 eq9
  have eq49 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq31
  have eq69 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) = X0 := superpose eq49 eq7
  have eq91 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq49 eq69
  have eq92 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq49 eq91
  have eq93 (X0 X1 : G) : X0 = X1 := superpose eq18 eq92
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq93 eq8
  subsumption eq98 eq93


@[equational_result]
theorem Equation7726_implies_Equation2 (G : Type*) [Magma G] (h : Equation7726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq44 eq15


@[equational_result]
theorem Equation7729_implies_Equation2 (G : Type*) [Magma G] (h : Equation7729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation7731_implies_Equation2 (G : Type*) [Magma G] (h : Equation7731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7732_implies_Equation2 (G : Type*) [Magma G] (h : Equation7732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7734_implies_Equation2 (G : Type*) [Magma G] (h : Equation7734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7735_implies_Equation2 (G : Type*) [Magma G] (h : Equation7735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7736_implies_Equation2 (G : Type*) [Magma G] (h : Equation7736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7738_implies_Equation2 (G : Type*) [Magma G] (h : Equation7738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3))) := superpose eq10 eq7
  have eq28 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq7 eq26
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq28 eq7
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq50 eq48


@[equational_result]
theorem Equation7740_implies_Equation2 (G : Type*) [Magma G] (h : Equation7740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation7742_implies_Equation2 (G : Type*) [Magma G] (h : Equation7742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7743_implies_Equation2 (G : Type*) [Magma G] (h : Equation7743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7744_implies_Equation2 (G : Type*) [Magma G] (h : Equation7744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7746_implies_Equation2 (G : Type*) [Magma G] (h : Equation7746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7747_implies_Equation2 (G : Type*) [Magma G] (h : Equation7747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7748_implies_Equation2 (G : Type*) [Magma G] (h : Equation7748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7750_implies_Equation2 (G : Type*) [Magma G] (h : Equation7750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7751_implies_Equation2 (G : Type*) [Magma G] (h : Equation7751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7752_implies_Equation2 (G : Type*) [Magma G] (h : Equation7752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7753_implies_Equation2 (G : Type*) [Magma G] (h : Equation7753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7757_implies_Equation2 (G : Type*) [Magma G] (h : Equation7757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation7759_implies_Equation2 (G : Type*) [Magma G] (h : Equation7759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) = (((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)))))) := superpose eq7 eq10
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X2) = ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) ◇ X2)) := superpose eq7 eq26
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq26 eq7
  have eq48 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) := superpose eq40 eq26
  have eq64 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = (X2 ◇ (X2 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2))) := superpose eq7 eq40
  have eq65 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)))) = (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)))) := superpose eq10 eq40
  have eq73 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := superpose eq40 eq7
  have eq76 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ X0)))) := superpose eq40 eq7
  have eq116 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) = (X0 ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))))) := superpose eq10 eq73
  have eq124 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))) := superpose eq73 eq10
  have eq131 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))) = (X0 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ X0)) := superpose eq73 eq40
  have eq133 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) ◇ X0)) := superpose eq124 eq131
  have eq161 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))) = (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))) := superpose eq11 eq40
  have eq171 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X4 ◇ ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) = ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))))) := superpose eq11 eq40
  have eq172 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = (((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))))) ◇ (((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))))) ◇ (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))))) := superpose eq11 eq48
  have eq175 (X0 X1 X2 X3 : G) : ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))))) = ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0))) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) := superpose eq76 eq171
  have eq176 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = (((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))))) ◇ ((X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))))) := superpose eq76 eq172
  have eq177 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = (((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))))) ◇ ((X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ (((X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))))) := superpose eq161 eq176
  have eq178 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = (((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))))) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq7 eq177
  have eq179 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0))) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq175 eq178
  have eq181 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)))) = ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X3 ◇ (((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))))) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)))) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq7 eq133
  have eq182 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) = ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((X3 ◇ (((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) := superpose eq10 eq133
  have eq208 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)))) = ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1))) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))))) := superpose eq76 eq181
  have eq210 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq208 eq179
  have eq212 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) = ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))) := superpose eq76 eq182
  have eq213 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) = ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)))))) := superpose eq65 eq212
  have eq214 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ X0) = ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))) := superpose eq7 eq213
  have eq215 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) = (X0 ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) ◇ X0))) := superpose eq214 eq116
  have eq218 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq31 eq215
  have eq219 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X2 := superpose eq218 eq10
  have eq226 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = (X2 ◇ (X2 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2))) := superpose eq218 eq64
  have eq231 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)))) = ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))))) := superpose eq226 eq208
  have eq234 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq73 eq231
  have eq238 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq234 eq210
  have eq251 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := superpose eq219 eq238
  have eq252 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq251 eq7
  have eq604 (X0 X2 : G) : X0 = X2 := superpose eq252 eq252
  have eq606 (X0 : G) : sK0 ≠ X0 := superpose eq604 eq8
  subsumption eq606 eq604


@[equational_result]
theorem Equation7760_implies_Equation2 (G : Type*) [Magma G] (h : Equation7760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ X3))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X0 ◇ X2))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) = (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (((X2 ◇ (X3 ◇ X0)) ◇ X2) ◇ (X3 ◇ X0)) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) = (((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X3)) ◇ (((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X3)) ◇ ((X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X4))) := superpose eq10 eq9
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X2) ◇ X3)) = ((((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X2) ◇ X3)) ◇ ((X4 ◇ X0) ◇ X4)) ◇ ((((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X2) ◇ X3)) ◇ ((X4 ◇ X0) ◇ X4)) ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) ◇ X5))) := superpose eq9 eq9
  have eq28 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = ((X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) ◇ ((X4 ◇ X3) ◇ X4)) := superpose eq9 eq10
  have eq35 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X3)) = (((X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X4) ◇ (((X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X4) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) := superpose eq10 eq13
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X2) ◇ X3)) ◇ ((X4 ◇ X0) ◇ X4)) = (((X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) ◇ X5) ◇ (((X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) ◇ X5) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)))) := superpose eq9 eq13
  have eq68 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X3)) = X1 := superpose eq10 eq35
  have eq69 (X0 X1 X2 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) = (X1 ◇ (X1 ◇ ((X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X4))) := superpose eq68 eq18
  have eq71 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq7 eq69
  have eq75 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq71 eq10
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X2) ◇ X3)) ◇ ((X4 ◇ X0) ◇ X4)) = (((X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) ◇ X5) ◇ (X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)))) := superpose eq71 eq36
  have eq78 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X2) ◇ X3)) ◇ ((X4 ◇ X0) ◇ X4)) := superpose eq75 eq77
  have eq79 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X2) ◇ X3)) = (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) ◇ X5))) := superpose eq78 eq19
  have eq81 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := superpose eq7 eq79
  have eq83 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X0 := superpose eq81 eq28
  have eq87 (X0 X2 X3 : G) : (((X2 ◇ (X3 ◇ X0)) ◇ X2) ◇ (X3 ◇ X0)) = X0 := superpose eq83 eq14
  have eq89 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq87 eq71
  have eq90 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq89 eq7
  have eq102 (X0 X3 : G) : X0 = X3 := superpose eq90 eq90
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq104 eq102


@[equational_result]
theorem Equation7761_implies_Equation2 (G : Type*) [Magma G] (h : Equation7761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation7765_implies_Equation2 (G : Type*) [Magma G] (h : Equation7765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq30 eq18


@[equational_result]
theorem Equation7767_implies_Equation2 (G : Type*) [Magma G] (h : Equation7767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation7768_implies_Equation2 (G : Type*) [Magma G] (h : Equation7768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation7769_implies_Equation2 (G : Type*) [Magma G] (h : Equation7769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X4)))) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq55 eq22


@[equational_result]
theorem Equation7770_implies_Equation2 (G : Type*) [Magma G] (h : Equation7770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq34 eq16


@[equational_result]
theorem Equation7772_implies_Equation2 (G : Type*) [Magma G] (h : Equation7772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1)) = (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ ((X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X2))) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq10 eq10
  have eq19 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := superpose eq7 eq10
  have eq28 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := superpose eq20 eq19
  have eq30 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X1 ◇ (X1 ◇ ((X4 ◇ (X1 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X1))) := superpose eq7 eq9
  have eq32 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1)) = (X1 ◇ (X1 ◇ ((X4 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1))) := superpose eq10 eq9
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X0 ◇ ((X5 ◇ ((X4 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0))) = (X0 ◇ ((X3 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ X0)) := superpose eq9 eq9
  have eq36 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0)) = (X0 ◇ (X0 ◇ ((X4 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X0))) := superpose eq9 eq9
  have eq37 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1)) = (X1 ◇ (X1 ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X1))) := superpose eq10 eq9
  have eq39 (X0 X1 X2 X4 : G) : (X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X0)) = (X0 ◇ (X0 ◇ ((X4 ◇ X1) ◇ X0))) := superpose eq10 eq9
  have eq69 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X1 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1)) := superpose eq7 eq32
  have eq70 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X2)) := superpose eq69 eq11
  have eq78 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq69 eq33
  have eq79 (X0 X2 X3 X4 : G) : (X2 ◇ X0) = (X0 ◇ (X0 ◇ ((X4 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X0))) := superpose eq69 eq36
  have eq80 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq70 eq37
  have eq81 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ ((X4 ◇ X1) ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0))) := superpose eq70 eq39
  have eq82 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ ((X4 ◇ X1) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)))) := superpose eq70 eq81
  have eq83 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X4 ◇ X1) ◇ X0))) := superpose eq7 eq82
  have eq85 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq83 eq78
  have eq92 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X1 ◇ (X1 ◇ ((X4 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1))) := superpose eq85 eq30
  have eq98 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq85 eq92
  have eq99 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = (X1 ◇ X1) := superpose eq83 eq98
  have eq100 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq99 eq80
  have eq101 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq99 eq79
  have eq102 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq99 eq85
  have eq109 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := superpose eq101 eq16
  have eq110 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := superpose eq109 eq28
  have eq112 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose eq100 eq110
  have eq119 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq102 eq112
  have eq184 (X0 X2 : G) : X0 = X2 := superpose eq119 eq119
  have eq195 (X0 : G) : sK0 ≠ X0 := superpose eq184 eq8
  subsumption eq195 eq184


@[equational_result]
theorem Equation7774_implies_Equation2 (G : Type*) [Magma G] (h : Equation7774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation7776_implies_Equation2 (G : Type*) [Magma G] (h : Equation7776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7777_implies_Equation2 (G : Type*) [Magma G] (h : Equation7777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7778_implies_Equation2 (G : Type*) [Magma G] (h : Equation7778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7780_implies_Equation2 (G : Type*) [Magma G] (h : Equation7780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7781_implies_Equation2 (G : Type*) [Magma G] (h : Equation7781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7782_implies_Equation2 (G : Type*) [Magma G] (h : Equation7782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7784_implies_Equation2 (G : Type*) [Magma G] (h : Equation7784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7785_implies_Equation2 (G : Type*) [Magma G] (h : Equation7785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7786_implies_Equation2 (G : Type*) [Magma G] (h : Equation7786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7787_implies_Equation2 (G : Type*) [Magma G] (h : Equation7787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7789_implies_Equation2 (G : Type*) [Magma G] (h : Equation7789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq19 (X0 X2 X4 : G) : (X4 ◇ (X4 ◇ (X2 ◇ X4))) = X0 := superpose eq7 eq10
  have eq102 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq201 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq201 eq102


@[equational_result]
theorem Equation7790_implies_Equation2 (G : Type*) [Magma G] (h : Equation7790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X3)) = (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq7 eq10
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = X1 := superpose eq10 eq7
  have eq28 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ (X3 ◇ X4)) ◇ X3) ◇ (((X3 ◇ (X3 ◇ X4)) ◇ X3) ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X4 := superpose eq10 eq7
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X5 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = (X3 ◇ ((X4 ◇ (X4 ◇ (X3 ◇ X1))) ◇ X4)) := superpose eq10 eq9
  have eq56 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) = (X3 ◇ ((X4 ◇ (X4 ◇ (X3 ◇ X2))) ◇ X4)) := superpose eq9 eq9
  have eq81 (X1 X3 X4 : G) : (X3 ◇ ((X4 ◇ (X4 ◇ (X3 ◇ X1))) ◇ X4)) = X1 := superpose eq26 eq52
  have eq82 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))) = X2 := superpose eq81 eq56
  have eq106 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ X3) := superpose eq10 eq21
  have eq123 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ ((X3 ◇ X2) ◇ X3))) = (X3 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X0)) := superpose eq21 eq9
  have eq144 (X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ (X4 ◇ ((X3 ◇ X2) ◇ X3))) := superpose eq24 eq123
  have eq150 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X2 := superpose eq144 eq82
  have eq158 (X1 X2 X3 : G) : (X3 ◇ (X3 ◇ (X1 ◇ X2))) = X1 := superpose eq150 eq26
  have eq160 (X1 X2 X3 X4 : G) : ((((X3 ◇ (X3 ◇ X4)) ◇ X3) ◇ (((X3 ◇ (X3 ◇ X4)) ◇ X3) ◇ X1)) ◇ (X1 ◇ X2)) = X4 := superpose eq150 eq28
  have eq212 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq158 eq106
  have eq231 (X1 X3 X4 : G) : ((((X3 ◇ (X3 ◇ X4)) ◇ X3) ◇ (((X3 ◇ (X3 ◇ X4)) ◇ X3) ◇ X1)) ◇ X1) = X4 := superpose eq212 eq160
  have eq232 (X1 X3 X4 : G) : (((X3 ◇ (X3 ◇ X4)) ◇ X3) ◇ X1) = X4 := superpose eq212 eq231
  have eq233 (X1 X3 X4 : G) : ((X3 ◇ (X3 ◇ X4)) ◇ X1) = X4 := superpose eq212 eq232
  have eq234 (X1 X3 X4 : G) : (X3 ◇ X1) = X4 := superpose eq212 eq233
  have eq235 (X0 X3 : G) : X0 = X3 := superpose eq234 eq234
  have eq237 (X0 : G) : sK0 ≠ X0 := superpose eq235 eq8
  subsumption eq237 eq235


@[equational_result]
theorem Equation7791_implies_Equation2 (G : Type*) [Magma G] (h : Equation7791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq30 eq18


@[equational_result]
theorem Equation7793_implies_Equation2 (G : Type*) [Magma G] (h : Equation7793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7794_implies_Equation2 (G : Type*) [Magma G] (h : Equation7794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7795_implies_Equation2 (G : Type*) [Magma G] (h : Equation7795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7797_implies_Equation2 (G : Type*) [Magma G] (h : Equation7797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7798_implies_Equation2 (G : Type*) [Magma G] (h : Equation7798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7799_implies_Equation2 (G : Type*) [Magma G] (h : Equation7799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7801_implies_Equation2 (G : Type*) [Magma G] (h : Equation7801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7802_implies_Equation2 (G : Type*) [Magma G] (h : Equation7802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7803_implies_Equation2 (G : Type*) [Magma G] (h : Equation7803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7804_implies_Equation2 (G : Type*) [Magma G] (h : Equation7804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7806_implies_Equation2 (G : Type*) [Magma G] (h : Equation7806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq19 (X0 X3 X6 : G) : (X6 ◇ (X6 ◇ (X3 ◇ X6))) = X0 := superpose eq7 eq10
  have eq106 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq208 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq208 eq106


@[equational_result]
theorem Equation7807_implies_Equation2 (G : Type*) [Magma G] (h : Equation7807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X3 ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X1) := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) ◇ X1) = X0 := superpose eq7 eq10
  have eq38 (X0 X1 X2 X3 X4 X6 X7 : G) : ((((X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3) ◇ (X6 ◇ X7)) ◇ X4) = X7 := superpose eq10 eq11
  have eq60 (X2 X4 X6 X7 : G) : ((X2 ◇ (X6 ◇ X7)) ◇ X4) = X7 := superpose eq25 eq38
  have eq69 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq60 eq22
  have eq80 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) = X0 := superpose eq69 eq25
  have eq92 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq69 eq80
  have eq95 (X0 X1 : G) : X0 = X1 := superpose eq69 eq92
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq100 eq95


@[equational_result]
theorem Equation7808_implies_Equation2 (G : Type*) [Magma G] (h : Equation7808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X3) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq51 (X0 X6 X7 : G) : (X0 ◇ X6) = X7 := superpose eq11 eq11
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq7 eq51
  have eq194 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq194 eq64


@[equational_result]
theorem Equation7809_implies_Equation2 (G : Type*) [Magma G] (h : Equation7809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ (X1 ◇ X0)) = X4 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq30 eq18


@[equational_result]
theorem Equation7811_implies_Equation2 (G : Type*) [Magma G] (h : Equation7811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7812_implies_Equation2 (G : Type*) [Magma G] (h : Equation7812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7813_implies_Equation2 (G : Type*) [Magma G] (h : Equation7813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7814_implies_Equation2 (G : Type*) [Magma G] (h : Equation7814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7816_implies_Equation2 (G : Type*) [Magma G] (h : Equation7816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7817_implies_Equation2 (G : Type*) [Magma G] (h : Equation7817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7818_implies_Equation2 (G : Type*) [Magma G] (h : Equation7818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7819_implies_Equation2 (G : Type*) [Magma G] (h : Equation7819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7821_implies_Equation2 (G : Type*) [Magma G] (h : Equation7821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7822_implies_Equation2 (G : Type*) [Magma G] (h : Equation7822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7823_implies_Equation2 (G : Type*) [Magma G] (h : Equation7823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7824_implies_Equation2 (G : Type*) [Magma G] (h : Equation7824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7826_implies_Equation2 (G : Type*) [Magma G] (h : Equation7826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7827_implies_Equation2 (G : Type*) [Magma G] (h : Equation7827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7828_implies_Equation2 (G : Type*) [Magma G] (h : Equation7828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7829_implies_Equation2 (G : Type*) [Magma G] (h : Equation7829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7830_implies_Equation2 (G : Type*) [Magma G] (h : Equation7830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7832_implies_Equation2 (G : Type*) [Magma G] (h : Equation7832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation7833_implies_Equation2 (G : Type*) [Magma G] (h : Equation7833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation7834_implies_Equation2 (G : Type*) [Magma G] (h : Equation7834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7836_implies_Equation2 (G : Type*) [Magma G] (h : Equation7836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation7838_implies_Equation2 (G : Type*) [Magma G] (h : Equation7838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7841_implies_Equation2 (G : Type*) [Magma G] (h : Equation7841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq9
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq61 eq26


@[equational_result]
theorem Equation7842_implies_Equation2 (G : Type*) [Magma G] (h : Equation7842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7844_implies_Equation2 (G : Type*) [Magma G] (h : Equation7844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation7845_implies_Equation2 (G : Type*) [Magma G] (h : Equation7845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation7846_implies_Equation2 (G : Type*) [Magma G] (h : Equation7846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation7847_implies_Equation2 (G : Type*) [Magma G] (h : Equation7847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7849_implies_Equation2 (G : Type*) [Magma G] (h : Equation7849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation7850_implies_Equation2 (G : Type*) [Magma G] (h : Equation7850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X0)) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X1 := superpose eq10 eq10
  have eq50 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq165 eq50


@[equational_result]
theorem Equation7851_implies_Equation2 (G : Type*) [Magma G] (h : Equation7851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation7853_implies_Equation2 (G : Type*) [Magma G] (h : Equation7853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq44 eq17


@[equational_result]
theorem Equation7855_implies_Equation2 (G : Type*) [Magma G] (h : Equation7855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation7859_implies_Equation2 (G : Type*) [Magma G] (h : Equation7859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7861_implies_Equation2 (G : Type*) [Magma G] (h : Equation7861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq50 eq18


@[equational_result]
theorem Equation7862_implies_Equation2 (G : Type*) [Magma G] (h : Equation7862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation7863_implies_Equation2 (G : Type*) [Magma G] (h : Equation7863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq50 eq12


@[equational_result]
theorem Equation7864_implies_Equation2 (G : Type*) [Magma G] (h : Equation7864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7867_implies_Equation2 (G : Type*) [Magma G] (h : Equation7867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X2) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X1 ◇ (X0 ◇ X1))) = (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq10 eq10
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq10 eq10
  have eq28 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ (X1 ◇ X2))))) = X1 := superpose eq10 eq7
  have eq36 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq10 eq21
  have eq37 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X3 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq24 eq36
  have eq40 (X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2))) = X1 := superpose eq10 eq28
  have eq41 (X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2))) = X1 := superpose eq24 eq40
  have eq42 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq41 eq37
  have eq43 (X1 X2 X3 : G) : (X3 ◇ X2) = X1 := superpose eq42 eq41
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq58 eq56


@[equational_result]
theorem Equation7868_implies_Equation2 (G : Type*) [Magma G] (h : Equation7868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7872_implies_Equation2 (G : Type*) [Magma G] (h : Equation7872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7875_implies_Equation2 (G : Type*) [Magma G] (h : Equation7875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq9
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq33 eq23


@[equational_result]
theorem Equation7876_implies_Equation2 (G : Type*) [Magma G] (h : Equation7876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation7878_implies_Equation2 (G : Type*) [Magma G] (h : Equation7878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation7879_implies_Equation2 (G : Type*) [Magma G] (h : Equation7879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq50 eq18


@[equational_result]
theorem Equation7880_implies_Equation2 (G : Type*) [Magma G] (h : Equation7880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq29 eq16


@[equational_result]
theorem Equation7881_implies_Equation2 (G : Type*) [Magma G] (h : Equation7881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7883_implies_Equation2 (G : Type*) [Magma G] (h : Equation7883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation7884_implies_Equation2 (G : Type*) [Magma G] (h : Equation7884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation7885_implies_Equation2 (G : Type*) [Magma G] (h : Equation7885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7886_implies_Equation2 (G : Type*) [Magma G] (h : Equation7886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7888_implies_Equation2 (G : Type*) [Magma G] (h : Equation7888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq53 eq20


@[equational_result]
theorem Equation7889_implies_Equation2 (G : Type*) [Magma G] (h : Equation7889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1)) ◇ (X4 ◇ ((X5 ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ (X0 ◇ X4))) = X2 := superpose eq7 eq7
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq10 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq51 eq40


@[equational_result]
theorem Equation7890_implies_Equation2 (G : Type*) [Magma G] (h : Equation7890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation7891_implies_Equation2 (G : Type*) [Magma G] (h : Equation7891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7893_implies_Equation2 (G : Type*) [Magma G] (h : Equation7893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X4) ◇ X0) = X2 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X3 := superpose eq7 eq12
  have eq59 (X0 X5 : G) : X0 = X5 := superpose eq12 eq33
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq149 eq59


@[equational_result]
theorem Equation7894_implies_Equation2 (G : Type*) [Magma G] (h : Equation7894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X2)) ◇ ((X4 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X2))))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X2)) ◇ X0)) = X4 := superpose eq7 eq9
  have eq27 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq81 eq27


@[equational_result]
theorem Equation7895_implies_Equation2 (G : Type*) [Magma G] (h : Equation7895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation7896_implies_Equation2 (G : Type*) [Magma G] (h : Equation7896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7898_implies_Equation2 (G : Type*) [Magma G] (h : Equation7898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation7899_implies_Equation2 (G : Type*) [Magma G] (h : Equation7899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation7900_implies_Equation2 (G : Type*) [Magma G] (h : Equation7900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation7901_implies_Equation2 (G : Type*) [Magma G] (h : Equation7901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7903_implies_Equation2 (G : Type*) [Magma G] (h : Equation7903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation7904_implies_Equation2 (G : Type*) [Magma G] (h : Equation7904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation7905_implies_Equation2 (G : Type*) [Magma G] (h : Equation7905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7906_implies_Equation2 (G : Type*) [Magma G] (h : Equation7906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation7907_implies_Equation2 (G : Type*) [Magma G] (h : Equation7907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7909_implies_Equation2 (G : Type*) [Magma G] (h : Equation7909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq54 eq16


@[equational_result]
theorem Equation7911_implies_Equation2 (G : Type*) [Magma G] (h : Equation7911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation7913_implies_Equation2 (G : Type*) [Magma G] (h : Equation7913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation7914_implies_Equation2 (G : Type*) [Magma G] (h : Equation7914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X3 ◇ (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X1 ◇ (X3 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq10 eq7
  have eq41 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X2))) = (((X4 ◇ (((X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X2)) ◇ X3) ◇ X4)) ◇ X0) ◇ ((X4 ◇ (((X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X2)) ◇ X3) ◇ X4)) ◇ ((X4 ◇ (((X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X2)) ◇ X3) ◇ X4)) ◇ X0))) := superpose eq9 eq19
  have eq44 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (X1 ◇ (X2 ◇ (((X3 ◇ (X0 ◇ X3)) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X2))) := superpose eq10 eq19
  have eq59 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X2)) = X1 := superpose eq19 eq10
  have eq82 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X2))) = X3 := superpose eq59 eq41
  have eq83 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq82 eq44
  have eq85 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq83 eq7
  have eq86 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3))) = X2 := superpose eq83 eq9
  have eq124 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq83 eq85
  have eq127 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) = X2 := superpose eq124 eq86
  have eq128 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X3) = X2 := superpose eq124 eq127
  have eq129 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = X2 := superpose eq124 eq128
  have eq130 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq124 eq129
  have eq131 (X0 X3 : G) : X0 = X3 := superpose eq130 eq130
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq136 eq131


@[equational_result]
theorem Equation7915_implies_Equation2 (G : Type*) [Magma G] (h : Equation7915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation7918_implies_Equation2 (G : Type*) [Magma G] (h : Equation7918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = (X1 ◇ (((X1 ◇ X0) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))))) := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X2) = (X1 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))))) := superpose eq7 eq10
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ ((X2 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0)) := superpose eq7 eq9
  have eq42 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq26 eq7
  have eq45 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq26 eq7
  have eq60 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq26 eq13
  have eq74 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))) := superpose eq42 eq9
  have eq94 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq74
  have eq134 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X0)) := superpose eq10 eq11
  have eq147 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0)) := superpose eq94 eq134
  have eq148 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq94 eq7
  have eq163 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2)) = X1 := superpose eq148 eq45
  have eq174 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) := superpose eq163 eq60
  have eq234 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose eq148 eq148
  have eq257 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq174 eq234
  have eq258 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq257 eq147
  have eq259 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq257 eq148
  have eq273 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq94 eq258
  have eq276 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq259 eq273
  have eq279 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq276 eq259
  have eq280 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) = X0 := superpose eq279 eq7
  have eq369 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq279 eq280
  have eq370 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq279 eq369
  have eq371 (X0 X1 : G) : X0 = X1 := superpose eq94 eq370
  have eq376 (X0 : G) : sK0 ≠ X0 := superpose eq371 eq8
  subsumption eq376 eq371


@[equational_result]
theorem Equation7919_implies_Equation2 (G : Type*) [Magma G] (h : Equation7919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7921_implies_Equation2 (G : Type*) [Magma G] (h : Equation7921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation7922_implies_Equation2 (G : Type*) [Magma G] (h : Equation7922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq62 eq17


@[equational_result]
theorem Equation7923_implies_Equation2 (G : Type*) [Magma G] (h : Equation7923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq61 eq12


@[equational_result]
theorem Equation7924_implies_Equation2 (G : Type*) [Magma G] (h : Equation7924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7926_implies_Equation2 (G : Type*) [Magma G] (h : Equation7926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq55 eq18


@[equational_result]
theorem Equation7928_implies_Equation2 (G : Type*) [Magma G] (h : Equation7928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7930_implies_Equation2 (G : Type*) [Magma G] (h : Equation7930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7931_implies_Equation2 (G : Type*) [Magma G] (h : Equation7931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7932_implies_Equation2 (G : Type*) [Magma G] (h : Equation7932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7934_implies_Equation2 (G : Type*) [Magma G] (h : Equation7934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7935_implies_Equation2 (G : Type*) [Magma G] (h : Equation7935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7936_implies_Equation2 (G : Type*) [Magma G] (h : Equation7936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7938_implies_Equation2 (G : Type*) [Magma G] (h : Equation7938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7939_implies_Equation2 (G : Type*) [Magma G] (h : Equation7939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7940_implies_Equation2 (G : Type*) [Magma G] (h : Equation7940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7941_implies_Equation2 (G : Type*) [Magma G] (h : Equation7941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7943_implies_Equation2 (G : Type*) [Magma G] (h : Equation7943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0))) = X2 := superpose eq12 eq12
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq12 eq12
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq15 eq10
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) = X2 := superpose eq16 eq14
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = X0 := superpose eq16 eq12
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq20 eq15
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X2 := superpose eq23 eq18
  have eq34 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq23 eq29
  have eq35 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq23 eq34
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation7944_implies_Equation2 (G : Type*) [Magma G] (h : Equation7944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X2) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2))))) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0)))) = X3 := superpose eq12 eq12
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq12 eq12
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0)))) = X3 := superpose eq14 eq13
  have eq19 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X3 := superpose eq14 eq15
  have eq20 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq14 eq19
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq26 eq21


@[equational_result]
theorem Equation7945_implies_Equation2 (G : Type*) [Magma G] (h : Equation7945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7947_implies_Equation2 (G : Type*) [Magma G] (h : Equation7947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7948_implies_Equation2 (G : Type*) [Magma G] (h : Equation7948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7949_implies_Equation2 (G : Type*) [Magma G] (h : Equation7949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7951_implies_Equation2 (G : Type*) [Magma G] (h : Equation7951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7952_implies_Equation2 (G : Type*) [Magma G] (h : Equation7952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation7953_implies_Equation2 (G : Type*) [Magma G] (h : Equation7953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7955_implies_Equation2 (G : Type*) [Magma G] (h : Equation7955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7956_implies_Equation2 (G : Type*) [Magma G] (h : Equation7956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7957_implies_Equation2 (G : Type*) [Magma G] (h : Equation7957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7958_implies_Equation2 (G : Type*) [Magma G] (h : Equation7958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7960_implies_Equation2 (G : Type*) [Magma G] (h : Equation7960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq67 eq19


@[equational_result]
theorem Equation7961_implies_Equation2 (G : Type*) [Magma G] (h : Equation7961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X4 ◇ X0)) ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq19 (X0 X1 X3 X6 : G) : (X1 ◇ (X6 ◇ (X3 ◇ X6))) = X0 := superpose eq7 eq10
  have eq106 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq222 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq222 eq106


@[equational_result]
theorem Equation7962_implies_Equation2 (G : Type*) [Magma G] (h : Equation7962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation7963_implies_Equation2 (G : Type*) [Magma G] (h : Equation7963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7965_implies_Equation2 (G : Type*) [Magma G] (h : Equation7965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7966_implies_Equation2 (G : Type*) [Magma G] (h : Equation7966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7967_implies_Equation2 (G : Type*) [Magma G] (h : Equation7967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7968_implies_Equation2 (G : Type*) [Magma G] (h : Equation7968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7970_implies_Equation2 (G : Type*) [Magma G] (h : Equation7970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7971_implies_Equation2 (G : Type*) [Magma G] (h : Equation7971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7972_implies_Equation2 (G : Type*) [Magma G] (h : Equation7972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7973_implies_Equation2 (G : Type*) [Magma G] (h : Equation7973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7975_implies_Equation2 (G : Type*) [Magma G] (h : Equation7975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7976_implies_Equation2 (G : Type*) [Magma G] (h : Equation7976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation7977_implies_Equation2 (G : Type*) [Magma G] (h : Equation7977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation7978_implies_Equation2 (G : Type*) [Magma G] (h : Equation7978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7980_implies_Equation2 (G : Type*) [Magma G] (h : Equation7980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7981_implies_Equation2 (G : Type*) [Magma G] (h : Equation7981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7982_implies_Equation2 (G : Type*) [Magma G] (h : Equation7982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7983_implies_Equation2 (G : Type*) [Magma G] (h : Equation7983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation7984_implies_Equation2 (G : Type*) [Magma G] (h : Equation7984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation7987_implies_Equation2 (G : Type*) [Magma G] (h : Equation7987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq66 eq22


@[equational_result]
theorem Equation7988_implies_Equation2 (G : Type*) [Magma G] (h : Equation7988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation7990_implies_Equation2 (G : Type*) [Magma G] (h : Equation7990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X3 ◇ ((X3 ◇ X0) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X3 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((X3 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X3 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)))))) = X1 := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X2 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1))))) = X1 := superpose eq7 eq10
  have eq15 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = X0 := superpose eq7 eq10
  have eq27 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)) := superpose eq7 eq9
  have eq36 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X1) = X1 := superpose eq7 eq15
  have eq39 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = X1 := superpose eq15 eq7
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq15 eq7
  have eq58 (X0 X2 : G) : ((X2 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose eq15 eq27
  have eq61 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq27 eq7
  have eq64 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq27 eq7
  have eq84 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = (X2 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq36 eq7
  have eq88 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = ((((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq36 eq15
  have eq95 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq36 eq88
  have eq137 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq27 eq39
  have eq156 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq61 eq137
  have eq157 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq61 eq156
  have eq216 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := superpose eq58 eq13
  have eq219 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq58 eq7
  have eq238 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq216
  have eq250 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X3 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X4))) ◇ ((X3 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X4)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X3 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X4)))))) := superpose eq27 eq11
  have eq252 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) ◇ ((X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))))) := superpose eq15 eq11
  have eq347 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X0 := superpose eq219 eq7
  have eq525 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq15 eq238
  have eq562 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq525 eq95
  have eq665 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := superpose eq347 eq562
  have eq667 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq665 eq84
  have eq681 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X2) = X0 := superpose eq667 eq44
  have eq696 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) ◇ ((X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)))))) = X0 := superpose eq681 eq252
  have eq708 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq681 eq157
  have eq710 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq696 eq250
  have eq713 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq710 eq64
  have eq726 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq710 eq708
  have eq737 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq726 eq713
  have eq752 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq525 eq737
  have eq756 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq752 eq61
  have eq787 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq752 eq756
  have eq792 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := superpose eq787 eq7
  have eq939 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq787 eq792
  have eq940 (X0 X3 : G) : X0 = X3 := superpose eq939 eq939
  have eq942 (X0 : G) : sK0 ≠ X0 := superpose eq940 eq8
  subsumption eq942 eq940


@[equational_result]
theorem Equation7991_implies_Equation2 (G : Type*) [Magma G] (h : Equation7991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) = X1 := superpose eq7 eq7
  have eq32 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X2 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))))) := superpose eq9 eq10
  have eq40 (X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq32
  have eq41 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq40 eq7
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3))) = X2 := superpose eq40 eq9
  have eq63 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq40 eq42
  have eq64 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq63 eq40
  have eq68 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq64 eq41
  have eq75 (X0 X2 : G) : X0 = X2 := superpose eq68 eq68
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq77 eq75


@[equational_result]
theorem Equation7992_implies_Equation2 (G : Type*) [Magma G] (h : Equation7992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7995_implies_Equation2 (G : Type*) [Magma G] (h : Equation7995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (((X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0) ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq9
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq64 eq27


@[equational_result]
theorem Equation7996_implies_Equation2 (G : Type*) [Magma G] (h : Equation7996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation7998_implies_Equation2 (G : Type*) [Magma G] (h : Equation7998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation7999_implies_Equation2 (G : Type*) [Magma G] (h : Equation7999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation8000_implies_Equation2 (G : Type*) [Magma G] (h : Equation8000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X4 ◇ ((X4 ◇ (X0 ◇ X5)) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq29 eq16


@[equational_result]
theorem Equation8001_implies_Equation2 (G : Type*) [Magma G] (h : Equation8001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8004_implies_Equation2 (G : Type*) [Magma G] (h : Equation8004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)) = (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2))) := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ X1) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) = X2 := superpose eq10 eq7
  have eq27 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X4 ◇ ((X4 ◇ (X3 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3))) ◇ X4))) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq9
  have eq70 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)))) ◇ X0) := superpose eq10 eq20
  have eq94 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))))))) = X2 := superpose eq20 eq7
  have eq116 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq21 eq20
  have eq128 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2))) := superpose eq116 eq14
  have eq133 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X2 ◇ (X4 ◇ ((X4 ◇ (X3 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X3)))) ◇ X4))) := superpose eq116 eq27
  have eq152 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))))) ◇ X0) := superpose eq116 eq70
  have eq187 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)))) := superpose eq116 eq128
  have eq189 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (X2 ◇ (X4 ◇ (X4 ◇ ((X3 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4)))) := superpose eq116 eq133
  have eq190 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X4 ◇ (X4 ◇ ((X3 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4)))) := superpose eq116 eq189
  have eq221 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ X0) := superpose eq21 eq152
  have eq231 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X1 ◇ X2)))) = X2 := superpose eq221 eq94
  have eq240 (X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq221 eq231
  have eq242 (X0 X2 X3 X4 : G) : (X2 ◇ (X4 ◇ (X4 ◇ ((X3 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X4)))) = X0 := superpose eq240 eq190
  have eq266 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq240 eq187
  have eq267 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X3)))) = X0 := superpose eq240 eq242
  have eq268 (X0 X2 : G) : (X2 ◇ (X2 ◇ X0)) = X0 := superpose eq240 eq267
  have eq270 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq268 eq20
  have eq280 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq268 eq270
  have eq358 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq280 eq266
  have eq370 (X0 X1 : G) : X0 = X1 := superpose eq280 eq358
  have eq372 (X0 : G) : sK0 ≠ X0 := superpose eq370 eq8
  subsumption eq372 eq370


@[equational_result]
theorem Equation8005_implies_Equation2 (G : Type*) [Magma G] (h : Equation8005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8007_implies_Equation2 (G : Type*) [Magma G] (h : Equation8007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation8008_implies_Equation2 (G : Type*) [Magma G] (h : Equation8008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation8009_implies_Equation2 (G : Type*) [Magma G] (h : Equation8009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8011_implies_Equation2 (G : Type*) [Magma G] (h : Equation8011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8012_implies_Equation2 (G : Type*) [Magma G] (h : Equation8012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8013_implies_Equation2 (G : Type*) [Magma G] (h : Equation8013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8015_implies_Equation2 (G : Type*) [Magma G] (h : Equation8015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8016_implies_Equation2 (G : Type*) [Magma G] (h : Equation8016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8017_implies_Equation2 (G : Type*) [Magma G] (h : Equation8017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8018_implies_Equation2 (G : Type*) [Magma G] (h : Equation8018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8021_implies_Equation2 (G : Type*) [Magma G] (h : Equation8021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq77 eq54


@[equational_result]
theorem Equation8022_implies_Equation2 (G : Type*) [Magma G] (h : Equation8022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8024_implies_Equation2 (G : Type*) [Magma G] (h : Equation8024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8025_implies_Equation2 (G : Type*) [Magma G] (h : Equation8025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8026_implies_Equation2 (G : Type*) [Magma G] (h : Equation8026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8028_implies_Equation2 (G : Type*) [Magma G] (h : Equation8028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8029_implies_Equation2 (G : Type*) [Magma G] (h : Equation8029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8030_implies_Equation2 (G : Type*) [Magma G] (h : Equation8030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8032_implies_Equation2 (G : Type*) [Magma G] (h : Equation8032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8033_implies_Equation2 (G : Type*) [Magma G] (h : Equation8033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8034_implies_Equation2 (G : Type*) [Magma G] (h : Equation8034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8035_implies_Equation2 (G : Type*) [Magma G] (h : Equation8035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8037_implies_Equation2 (G : Type*) [Magma G] (h : Equation8037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ X2) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 X5 X6 : G) : (X6 ◇ ((X4 ◇ ((X4 ◇ (X5 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (X3 ◇ X6))) = X0 := superpose eq7 eq10
  have eq24 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X3 ◇ (X4 ◇ (X5 ◇ (X6 ◇ X2)))) ◇ X7) = (X1 ◇ (X7 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq10 eq10
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = X2 := superpose eq10 eq7
  have eq41 (X2 X3 X4 X5 X6 X7 : G) : ((X3 ◇ (X4 ◇ (X5 ◇ (X6 ◇ X2)))) ◇ X7) = X2 := superpose eq31 eq24
  have eq42 (X0 X3 X6 : G) : (X6 ◇ X3) = X0 := superpose eq41 eq20
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq42
  have eq204 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq204 eq71


@[equational_result]
theorem Equation8038_implies_Equation2 (G : Type*) [Magma G] (h : Equation8038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) ◇ X0)) = X5 := superpose eq7 eq7
  have eq60 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq84 eq60


@[equational_result]
theorem Equation8039_implies_Equation2 (G : Type*) [Magma G] (h : Equation8039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ X0)) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation8040_implies_Equation2 (G : Type*) [Magma G] (h : Equation8040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8042_implies_Equation2 (G : Type*) [Magma G] (h : Equation8042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8043_implies_Equation2 (G : Type*) [Magma G] (h : Equation8043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8044_implies_Equation2 (G : Type*) [Magma G] (h : Equation8044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8045_implies_Equation2 (G : Type*) [Magma G] (h : Equation8045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8047_implies_Equation2 (G : Type*) [Magma G] (h : Equation8047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8048_implies_Equation2 (G : Type*) [Magma G] (h : Equation8048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8049_implies_Equation2 (G : Type*) [Magma G] (h : Equation8049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8050_implies_Equation2 (G : Type*) [Magma G] (h : Equation8050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8052_implies_Equation2 (G : Type*) [Magma G] (h : Equation8052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8053_implies_Equation2 (G : Type*) [Magma G] (h : Equation8053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8054_implies_Equation2 (G : Type*) [Magma G] (h : Equation8054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8055_implies_Equation2 (G : Type*) [Magma G] (h : Equation8055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8057_implies_Equation2 (G : Type*) [Magma G] (h : Equation8057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8058_implies_Equation2 (G : Type*) [Magma G] (h : Equation8058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8059_implies_Equation2 (G : Type*) [Magma G] (h : Equation8059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8060_implies_Equation2 (G : Type*) [Magma G] (h : Equation8060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8061_implies_Equation2 (G : Type*) [Magma G] (h : Equation8061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8063_implies_Equation2 (G : Type*) [Magma G] (h : Equation8063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq70 eq19


@[equational_result]
theorem Equation8064_implies_Equation2 (G : Type*) [Magma G] (h : Equation8064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation8065_implies_Equation2 (G : Type*) [Magma G] (h : Equation8065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8066_implies_Equation2 (G : Type*) [Magma G] (h : Equation8066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8068_implies_Equation2 (G : Type*) [Magma G] (h : Equation8068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq69 eq20


@[equational_result]
theorem Equation8069_implies_Equation2 (G : Type*) [Magma G] (h : Equation8069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) ◇ (X4 ◇ ((X5 ◇ X0) ◇ X4))) = X3 := superpose eq7 eq7
  have eq47 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq7
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq47
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq150 eq51


@[equational_result]
theorem Equation8070_implies_Equation2 (G : Type*) [Magma G] (h : Equation8070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation8071_implies_Equation2 (G : Type*) [Magma G] (h : Equation8071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8073_implies_Equation2 (G : Type*) [Magma G] (h : Equation8073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X4) ◇ X0) = X3 := superpose eq7 eq7
  have eq39 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq12 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq39
  have eq144 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq144 eq47


@[equational_result]
theorem Equation8074_implies_Equation2 (G : Type*) [Magma G] (h : Equation8074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ ((X4 ◇ X0) ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0)) = X5 := superpose eq7 eq9
  have eq27 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq64 eq27


@[equational_result]
theorem Equation8075_implies_Equation2 (G : Type*) [Magma G] (h : Equation8075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ X0)) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation8076_implies_Equation2 (G : Type*) [Magma G] (h : Equation8076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8078_implies_Equation2 (G : Type*) [Magma G] (h : Equation8078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation8079_implies_Equation2 (G : Type*) [Magma G] (h : Equation8079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation8080_implies_Equation2 (G : Type*) [Magma G] (h : Equation8080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8081_implies_Equation2 (G : Type*) [Magma G] (h : Equation8081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8083_implies_Equation2 (G : Type*) [Magma G] (h : Equation8083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation8084_implies_Equation2 (G : Type*) [Magma G] (h : Equation8084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation8085_implies_Equation2 (G : Type*) [Magma G] (h : Equation8085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8086_implies_Equation2 (G : Type*) [Magma G] (h : Equation8086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8087_implies_Equation2 (G : Type*) [Magma G] (h : Equation8087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8089_implies_Equation2 (G : Type*) [Magma G] (h : Equation8089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq71 eq20


@[equational_result]
theorem Equation8090_implies_Equation2 (G : Type*) [Magma G] (h : Equation8090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ (X1 ◇ X0)) ◇ X4)) = (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X3 ◇ X0)) ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) = X2 := superpose eq10 eq7
  have eq31 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4))) = X1 := superpose eq10 eq7
  have eq65 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ ((X4 ◇ (X5 ◇ (X6 ◇ X2))) ◇ X3)) = (X5 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq10 eq9
  have eq102 (X2 X3 X4 X5 X6 : G) : (X3 ◇ ((X4 ◇ (X5 ◇ (X6 ◇ X2))) ◇ X3)) = X2 := superpose eq29 eq65
  have eq106 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq102 eq31
  have eq107 (X0 X4 : G) : X0 = X4 := superpose eq7 eq106
  have eq225 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq225 eq107


@[equational_result]
theorem Equation8091_implies_Equation2 (G : Type*) [Magma G] (h : Equation8091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation8092_implies_Equation2 (G : Type*) [Magma G] (h : Equation8092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8094_implies_Equation2 (G : Type*) [Magma G] (h : Equation8094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8095_implies_Equation2 (G : Type*) [Magma G] (h : Equation8095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8096_implies_Equation2 (G : Type*) [Magma G] (h : Equation8096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8097_implies_Equation2 (G : Type*) [Magma G] (h : Equation8097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8099_implies_Equation2 (G : Type*) [Magma G] (h : Equation8099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8100_implies_Equation2 (G : Type*) [Magma G] (h : Equation8100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8101_implies_Equation2 (G : Type*) [Magma G] (h : Equation8101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8102_implies_Equation2 (G : Type*) [Magma G] (h : Equation8102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8104_implies_Equation2 (G : Type*) [Magma G] (h : Equation8104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8105_implies_Equation2 (G : Type*) [Magma G] (h : Equation8105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8106_implies_Equation2 (G : Type*) [Magma G] (h : Equation8106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8107_implies_Equation2 (G : Type*) [Magma G] (h : Equation8107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8109_implies_Equation2 (G : Type*) [Magma G] (h : Equation8109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8110_implies_Equation2 (G : Type*) [Magma G] (h : Equation8110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8111_implies_Equation2 (G : Type*) [Magma G] (h : Equation8111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8112_implies_Equation2 (G : Type*) [Magma G] (h : Equation8112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8113_implies_Equation2 (G : Type*) [Magma G] (h : Equation8113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8115_implies_Equation2 (G : Type*) [Magma G] (h : Equation8115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq58 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq12 eq12
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq58
  have eq202 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq202 eq68


@[equational_result]
theorem Equation8116_implies_Equation2 (G : Type*) [Magma G] (h : Equation8116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X0)) = X5 := superpose eq7 eq7
  have eq60 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq83 eq60


@[equational_result]
theorem Equation8117_implies_Equation2 (G : Type*) [Magma G] (h : Equation8117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ X0)) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation8118_implies_Equation2 (G : Type*) [Magma G] (h : Equation8118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8120_implies_Equation2 (G : Type*) [Magma G] (h : Equation8120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8121_implies_Equation2 (G : Type*) [Magma G] (h : Equation8121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8122_implies_Equation2 (G : Type*) [Magma G] (h : Equation8122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8123_implies_Equation2 (G : Type*) [Magma G] (h : Equation8123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X1)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8125_implies_Equation2 (G : Type*) [Magma G] (h : Equation8125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8126_implies_Equation2 (G : Type*) [Magma G] (h : Equation8126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8127_implies_Equation2 (G : Type*) [Magma G] (h : Equation8127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8128_implies_Equation2 (G : Type*) [Magma G] (h : Equation8128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X2)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8130_implies_Equation2 (G : Type*) [Magma G] (h : Equation8130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8131_implies_Equation2 (G : Type*) [Magma G] (h : Equation8131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8132_implies_Equation2 (G : Type*) [Magma G] (h : Equation8132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8133_implies_Equation2 (G : Type*) [Magma G] (h : Equation8133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8135_implies_Equation2 (G : Type*) [Magma G] (h : Equation8135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8136_implies_Equation2 (G : Type*) [Magma G] (h : Equation8136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8137_implies_Equation2 (G : Type*) [Magma G] (h : Equation8137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8138_implies_Equation2 (G : Type*) [Magma G] (h : Equation8138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8139_implies_Equation2 (G : Type*) [Magma G] (h : Equation8139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8141_implies_Equation2 (G : Type*) [Magma G] (h : Equation8141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq76 eq21


@[equational_result]
theorem Equation8142_implies_Equation2 (G : Type*) [Magma G] (h : Equation8142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation8143_implies_Equation2 (G : Type*) [Magma G] (h : Equation8143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8144_implies_Equation2 (G : Type*) [Magma G] (h : Equation8144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8146_implies_Equation2 (G : Type*) [Magma G] (h : Equation8146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8147_implies_Equation2 (G : Type*) [Magma G] (h : Equation8147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8148_implies_Equation2 (G : Type*) [Magma G] (h : Equation8148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8149_implies_Equation2 (G : Type*) [Magma G] (h : Equation8149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X1)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8151_implies_Equation2 (G : Type*) [Magma G] (h : Equation8151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8152_implies_Equation2 (G : Type*) [Magma G] (h : Equation8152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8153_implies_Equation2 (G : Type*) [Magma G] (h : Equation8153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8154_implies_Equation2 (G : Type*) [Magma G] (h : Equation8154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8156_implies_Equation2 (G : Type*) [Magma G] (h : Equation8156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8157_implies_Equation2 (G : Type*) [Magma G] (h : Equation8157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8158_implies_Equation2 (G : Type*) [Magma G] (h : Equation8158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8159_implies_Equation2 (G : Type*) [Magma G] (h : Equation8159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8161_implies_Equation2 (G : Type*) [Magma G] (h : Equation8161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8162_implies_Equation2 (G : Type*) [Magma G] (h : Equation8162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8163_implies_Equation2 (G : Type*) [Magma G] (h : Equation8163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8164_implies_Equation2 (G : Type*) [Magma G] (h : Equation8164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8165_implies_Equation2 (G : Type*) [Magma G] (h : Equation8165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8167_implies_Equation2 (G : Type*) [Magma G] (h : Equation8167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X6 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) = X6 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq79 eq22


@[equational_result]
theorem Equation8168_implies_Equation2 (G : Type*) [Magma G] (h : Equation8168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation8169_implies_Equation2 (G : Type*) [Magma G] (h : Equation8169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8170_implies_Equation2 (G : Type*) [Magma G] (h : Equation8170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8171_implies_Equation2 (G : Type*) [Magma G] (h : Equation8171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation8173_implies_Equation2 (G : Type*) [Magma G] (h : Equation8173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8174_implies_Equation2 (G : Type*) [Magma G] (h : Equation8174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8175_implies_Equation2 (G : Type*) [Magma G] (h : Equation8175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8176_implies_Equation2 (G : Type*) [Magma G] (h : Equation8176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8177_implies_Equation2 (G : Type*) [Magma G] (h : Equation8177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X1)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8179_implies_Equation2 (G : Type*) [Magma G] (h : Equation8179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8180_implies_Equation2 (G : Type*) [Magma G] (h : Equation8180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8181_implies_Equation2 (G : Type*) [Magma G] (h : Equation8181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8182_implies_Equation2 (G : Type*) [Magma G] (h : Equation8182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8183_implies_Equation2 (G : Type*) [Magma G] (h : Equation8183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8185_implies_Equation2 (G : Type*) [Magma G] (h : Equation8185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8186_implies_Equation2 (G : Type*) [Magma G] (h : Equation8186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8187_implies_Equation2 (G : Type*) [Magma G] (h : Equation8187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8188_implies_Equation2 (G : Type*) [Magma G] (h : Equation8188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8189_implies_Equation2 (G : Type*) [Magma G] (h : Equation8189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8191_implies_Equation2 (G : Type*) [Magma G] (h : Equation8191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8192_implies_Equation2 (G : Type*) [Magma G] (h : Equation8192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8193_implies_Equation2 (G : Type*) [Magma G] (h : Equation8193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8194_implies_Equation2 (G : Type*) [Magma G] (h : Equation8194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8195_implies_Equation2 (G : Type*) [Magma G] (h : Equation8195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8197_implies_Equation2 (G : Type*) [Magma G] (h : Equation8197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8198_implies_Equation2 (G : Type*) [Magma G] (h : Equation8198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8199_implies_Equation2 (G : Type*) [Magma G] (h : Equation8199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8200_implies_Equation2 (G : Type*) [Magma G] (h : Equation8200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8201_implies_Equation2 (G : Type*) [Magma G] (h : Equation8201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8202_implies_Equation2 (G : Type*) [Magma G] (h : Equation8202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X6))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation8408_implies_Equation2 (G : Type*) [Magma G] (h : Equation8408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq38 eq24


@[equational_result]
theorem Equation8411_implies_Equation2 (G : Type*) [Magma G] (h : Equation8411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2)) ◇ (X1 ◇ (X0 ◇ X3))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2)) ◇ X0) = X1 := superpose eq10 eq9
  have eq14 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq10 eq12
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq10 eq14
  have eq16 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq15 eq10
  have eq21 (X0 X1 : G) : X0 = X1 := superpose eq15 eq16
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation8413_implies_Equation2 (G : Type*) [Magma G] (h : Equation8413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9
  have eq19 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq15 eq11
  have eq24 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq15 eq19
  have eq25 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq24 eq15
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq24 eq25
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq40 eq30


@[equational_result]
theorem Equation8414_implies_Equation2 (G : Type*) [Magma G] (h : Equation8414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq37 eq23


@[equational_result]
theorem Equation8415_implies_Equation2 (G : Type*) [Magma G] (h : Equation8415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8418_implies_Equation2 (G : Type*) [Magma G] (h : Equation8418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation8421_implies_Equation2 (G : Type*) [Magma G] (h : Equation8421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation8423_implies_Equation2 (G : Type*) [Magma G] (h : Equation8423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq14 eq13
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq10 eq18
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq31 eq22


@[equational_result]
theorem Equation8425_implies_Equation2 (G : Type*) [Magma G] (h : Equation8425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8427_implies_Equation2 (G : Type*) [Magma G] (h : Equation8427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9
  have eq27 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq10
  have eq28 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ ((X2 ◇ X4) ◇ X2))) ◇ X0) = X2 := superpose eq7 eq10
  have eq34 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq27
  have eq88 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq10 eq17
  have eq114 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq10 eq88
  have eq137 (X0 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X4) ◇ X2))) ◇ X0) = X2 := superpose eq114 eq28
  have eq152 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X2 := superpose eq114 eq137
  have eq153 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq34 eq152
  have eq206 (X0 X2 : G) : X0 = X2 := superpose eq153 eq153
  have eq208 (X0 : G) : sK0 ≠ X0 := superpose eq206 eq8
  subsumption eq208 eq206


@[equational_result]
theorem Equation8428_implies_Equation2 (G : Type*) [Magma G] (h : Equation8428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (((X0 ◇ X3) ◇ X0) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq36 eq22


@[equational_result]
theorem Equation8429_implies_Equation2 (G : Type*) [Magma G] (h : Equation8429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq51 eq24


@[equational_result]
theorem Equation8431_implies_Equation2 (G : Type*) [Magma G] (h : Equation8431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) = X3 := superpose eq9 eq9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq9 eq9
  have eq35 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))))) := superpose eq13 eq13
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq13
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq13 eq7
  have eq48 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X0)) = (X2 ◇ (X3 ◇ X2)) := superpose eq9 eq35
  have eq65 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq12 eq12
  have eq83 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) = ((X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq13 eq42
  have eq103 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq42 eq9
  have eq105 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq9 eq83
  have eq123 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq105 eq65
  have eq128 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq103
  have eq130 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq128 eq123
  have eq132 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq128 eq37
  have eq133 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq132 eq130
  have eq134 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X1)) = X0 := superpose eq133 eq7
  have eq139 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq133 eq105
  have eq146 (X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = X2 := superpose eq139 eq48
  have eq157 (X0 X1 : G) : X0 = X1 := superpose eq134 eq146
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq157 eq8
  subsumption eq191 eq157


@[equational_result]
theorem Equation8433_implies_Equation2 (G : Type*) [Magma G] (h : Equation8433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4)) ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4)) ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq11 eq13
  have eq17 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq11 eq16
  have eq18 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq17 eq11
  have eq22 (X0 X1 : G) : X0 = X1 := superpose eq17 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation8436_implies_Equation2 (G : Type*) [Magma G] (h : Equation8436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ X3))) ◇ (X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq36 eq22


@[equational_result]
theorem Equation8437_implies_Equation2 (G : Type*) [Magma G] (h : Equation8437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ X4))) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8439_implies_Equation2 (G : Type*) [Magma G] (h : Equation8439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq21 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq16 eq12
  have eq27 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq16 eq21
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq10 eq27
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation8440_implies_Equation2 (G : Type*) [Magma G] (h : Equation8440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X5) ◇ (X0 ◇ (((X0 ◇ X3) ◇ X4) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq36 eq22


@[equational_result]
theorem Equation8441_implies_Equation2 (G : Type*) [Magma G] (h : Equation8441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (((X0 ◇ X4) ◇ X5) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq61 eq23


@[equational_result]
theorem Equation8442_implies_Equation2 (G : Type*) [Magma G] (h : Equation8442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8445_implies_Equation2 (G : Type*) [Magma G] (h : Equation8445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation8448_implies_Equation2 (G : Type*) [Magma G] (h : Equation8448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation8450_implies_Equation2 (G : Type*) [Magma G] (h : Equation8450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq14 eq13
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq10 eq18
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq31 eq22


@[equational_result]
theorem Equation8452_implies_Equation2 (G : Type*) [Magma G] (h : Equation8452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8455_implies_Equation2 (G : Type*) [Magma G] (h : Equation8455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation8458_implies_Equation2 (G : Type*) [Magma G] (h : Equation8458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := superpose eq9 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation8460_implies_Equation2 (G : Type*) [Magma G] (h : Equation8460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X1 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq14 eq13
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq9 eq18
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq30 eq21


@[equational_result]
theorem Equation8462_implies_Equation2 (G : Type*) [Magma G] (h : Equation8462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq22 eq14


@[equational_result]
theorem Equation8464_implies_Equation2 (G : Type*) [Magma G] (h : Equation8464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X1 ◇ X2))) = (X1 ◇ ((X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9
  have eq16 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ X4) ◇ X1) ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3))) = ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (((((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ X4) ◇ X1) ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3))) ◇ X0)) := superpose eq9 eq10
  have eq38 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq16 eq16
  have eq79 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq14 eq7
  have eq81 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq14 eq16
  have eq87 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq81 eq79
  have eq99 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ X4) ◇ X1) ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3))) = ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq87 eq29
  have eq123 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ X4) ◇ X1) ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq87 eq99
  have eq124 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ X4) ◇ X1) ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3))) = X0 := superpose eq38 eq123
  have eq125 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3))) = X0 := superpose eq87 eq124
  have eq126 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq81 eq125
  have eq127 (X0 X3 : G) : X0 = X3 := superpose eq9 eq126
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq127 eq8
  subsumption eq168 eq127


@[equational_result]
theorem Equation8466_implies_Equation2 (G : Type*) [Magma G] (h : Equation8466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq51 eq24


@[equational_result]
theorem Equation8468_implies_Equation2 (G : Type*) [Magma G] (h : Equation8468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1))) = X1 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq9 eq9
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq9 eq14
  have eq36 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq14 eq7
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) = ((X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq14 eq36
  have eq82 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = (X2 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq36 eq9
  have eq84 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq9 eq64
  have eq94 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq9 eq82
  have eq96 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq94 eq32
  have eq141 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq84 eq84
  have eq144 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq13 eq84
  have eq161 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq96 eq141
  have eq166 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) = X0 := superpose eq161 eq7
  have eq186 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq144 eq166
  have eq201 (X0 X2 : G) : X0 = X2 := superpose eq186 eq186
  have eq203 (X0 : G) : sK0 ≠ X0 := superpose eq201 eq8
  subsumption eq203 eq201


@[equational_result]
theorem Equation8470_implies_Equation2 (G : Type*) [Magma G] (h : Equation8470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = X0 := superpose eq10 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation8474_implies_Equation2 (G : Type*) [Magma G] (h : Equation8474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X2)) = X0 := superpose eq10 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation8476_implies_Equation2 (G : Type*) [Magma G] (h : Equation8476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq20 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq15 eq14
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq10 eq20
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq33 eq24


@[equational_result]
theorem Equation8477_implies_Equation2 (G : Type*) [Magma G] (h : Equation8477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X5) ◇ (X0 ◇ (((X1 ◇ X3) ◇ X4) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ X5)) = X2 := superpose eq10 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation8478_implies_Equation2 (G : Type*) [Magma G] (h : Equation8478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((((X1 ◇ X3) ◇ X4) ◇ X5) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq10
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X3)) = X0 := superpose eq12 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq13 eq13
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation8479_implies_Equation2 (G : Type*) [Magma G] (h : Equation8479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8481_implies_Equation2 (G : Type*) [Magma G] (h : Equation8481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X4 ◇ X5) ◇ X5))) ◇ (X5 ◇ (X0 ◇ X1))) = X5 := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X1))) := superpose eq10 eq7
  have eq28 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) = X0 := superpose eq7 eq18
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq18 eq18
  have eq74 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq10 eq28
  have eq77 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq28
  have eq138 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq77 eq7
  have eq200 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) ◇ ((X3 ◇ X2) ◇ X2))) ◇ X0) = X2 := superpose eq7 eq13
  have eq304 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq7 eq74
  have eq322 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose eq138 eq74
  have eq331 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq13 eq74
  have eq342 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq74 eq28
  have eq393 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq304 eq331
  have eq400 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq342 eq393
  have eq401 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ ((X3 ◇ X2) ◇ X2))) ◇ X0) = X2 := superpose eq400 eq200
  have eq409 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq400 eq36
  have eq439 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq400 eq409
  have eq440 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq342 eq439
  have eq445 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := superpose eq440 eq322
  have eq472 (X0 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (((X0 ◇ X0) ◇ X2) ◇ ((X3 ◇ X2) ◇ X2))) ◇ X0) = X2 := superpose eq440 eq401
  have eq485 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq342 eq445
  have eq510 (X0 X2 : G) : (((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (((X0 ◇ X0) ◇ X2) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq440 eq472
  have eq511 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq485 eq510
  have eq512 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq485 eq511
  have eq720 (X0 X2 : G) : X0 = X2 := superpose eq512 eq512
  have eq728 (X0 : G) : sK0 ≠ X0 := superpose eq720 eq8
  subsumption eq728 eq720


@[equational_result]
theorem Equation8482_implies_Equation2 (G : Type*) [Magma G] (h : Equation8482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq37 eq23


@[equational_result]
theorem Equation8483_implies_Equation2 (G : Type*) [Magma G] (h : Equation8483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq38 eq24


@[equational_result]
theorem Equation8487_implies_Equation2 (G : Type*) [Magma G] (h : Equation8487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4)) ◇ (X3 ◇ (X0 ◇ X5))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4)) ◇ X0) = X3 := superpose eq11 eq10
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq11 eq13
  have eq17 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq11 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq26 eq18


@[equational_result]
theorem Equation8490_implies_Equation2 (G : Type*) [Magma G] (h : Equation8490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (((X3 ◇ X0) ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq37 eq23


@[equational_result]
theorem Equation8491_implies_Equation2 (G : Type*) [Magma G] (h : Equation8491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8493_implies_Equation2 (G : Type*) [Magma G] (h : Equation8493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq10 eq16
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq33 eq29


@[equational_result]
theorem Equation8494_implies_Equation2 (G : Type*) [Magma G] (h : Equation8494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation8495_implies_Equation2 (G : Type*) [Magma G] (h : Equation8495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (((X4 ◇ X0) ◇ X5) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq37 eq23


@[equational_result]
theorem Equation8496_implies_Equation2 (G : Type*) [Magma G] (h : Equation8496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8498_implies_Equation2 (G : Type*) [Magma G] (h : Equation8498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ (X3 ◇ ((X0 ◇ X3) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X4 ◇ X1) ◇ X0) ◇ X1)) = ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ ((X0 ◇ (((X4 ◇ X1) ◇ X0) ◇ X1)) ◇ (X0 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))))) := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X2))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq40 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq17
  have eq42 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)))) = (((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ (((X4 ◇ X0) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)))) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)))) := superpose eq9 eq17
  have eq45 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ (((X3 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ X2))) ◇ X0) = X2 := superpose eq7 eq17
  have eq54 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1)))) = X2 := superpose eq17 eq7
  have eq93 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) ◇ X1)) := superpose eq7 eq40
  have eq106 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq40 eq17
  have eq109 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))))) := superpose eq40 eq7
  have eq123 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq54 eq106
  have eq170 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ (X0 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)))) = (((X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)) ◇ (((X5 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)))) ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ (X0 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)))) ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)))) := superpose eq11 eq17
  have eq173 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq123 eq40
  have eq275 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq173 eq17
  have eq376 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X0))) = X3 := superpose eq7 eq54
  have eq536 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq17 eq376
  have eq553 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq376 eq376
  have eq595 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq376 eq40
  have eq610 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq536 eq109
  have eq613 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq595 eq275
  have eq614 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq613 eq595
  have eq615 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq173 eq614
  have eq616 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq615 eq610
  have eq792 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq615 eq40
  have eq797 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq615 eq792
  have eq1179 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ X2) = (((X2 ◇ X2) ◇ X0) ◇ X2) := superpose eq7 eq616
  have eq1191 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq615 eq616
  have eq1261 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) ◇ ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ X0)) ◇ (((X4 ◇ X1) ◇ (((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) ◇ ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ X0))) ◇ X1)) = ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ (((((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) ◇ ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ X0)) ◇ (((X4 ◇ X1) ◇ (((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) ◇ ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ X0))) ◇ X1)) ◇ (X0 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))))) := superpose eq616 eq11
  have eq1275 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) := superpose eq1179 eq93
  have eq1276 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ (((X3 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) ◇ (((X2 ◇ X2) ◇ X0) ◇ X2))) ◇ X0) = X2 := superpose eq1179 eq45
  have eq1287 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq553 eq1191
  have eq1289 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq1287 eq797
  have eq1292 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq615 eq1289
  have eq1308 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ (((X3 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq1292 eq1276
  have eq1309 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq1292 eq1275
  have eq1328 (X0 X1 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ X3)))) = (((X1 ◇ (X3 ◇ X3)) ◇ (((X4 ◇ X0) ◇ (X1 ◇ (X3 ◇ X3))) ◇ X0)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ X3)))) ◇ (X1 ◇ (X3 ◇ X3)))) := superpose eq1292 eq42
  have eq1357 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)))) = (((X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)) ◇ (((X5 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4))) ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)))) ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)))) := superpose eq1292 eq170
  have eq1546 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq1292 eq1308
  have eq1547 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ X2) ◇ X0) = X2 := superpose eq615 eq1546
  have eq1548 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq1292 eq1547
  have eq1559 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq1548 eq1309
  have eq1560 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) = X1 := superpose eq615 eq1559
  have eq1561 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq1292 eq1560
  have eq1576 (X0 X1 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ X3)))) = (((X1 ◇ (X3 ◇ X3)) ◇ (((X4 ◇ X0) ◇ (X1 ◇ (X3 ◇ X3))) ◇ X0)) ◇ ((X1 ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X3 ◇ X3)))) := superpose eq1292 eq1328
  have eq1577 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ X3)))) := superpose eq1561 eq1576
  have eq1578 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X3)) = X3 := superpose eq1561 eq1577
  have eq1612 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)))) = (((X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)) ◇ (((X5 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4))) ◇ (X0 ◇ (X2 ◇ X2)))) ◇ ((X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)) ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)))) := superpose eq1292 eq1357
  have eq1613 (X0 X2 X3 X4 : G) : (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)) = ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ (((X3 ◇ X4) ◇ X2) ◇ X4)))) := superpose eq1561 eq1612
  have eq1614 (X0 X2 X4 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X4)) = X4 := superpose eq1578 eq1613
  have eq1615 (X0 X2 X4 : G) : (X2 ◇ (X0 ◇ X4)) = X4 := superpose eq1561 eq1614
  have eq1919 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) = ((((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) ◇ ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ X0)) ◇ (((X4 ◇ X1) ◇ (((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) ◇ ((X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3)) ◇ X0))) ◇ X1)) := superpose eq1615 eq1261
  have eq1920 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) = X1 := superpose eq1615 eq1919
  have eq1921 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq1615 eq1920
  have eq1940 (X0 X2 : G) : X0 = X2 := superpose eq615 eq1921
  have eq1976 (X0 : G) : sK0 ≠ X0 := superpose eq1940 eq8
  subsumption eq1976 eq1940


@[equational_result]
theorem Equation8500_implies_Equation2 (G : Type*) [Magma G] (h : Equation8500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X1) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq38 eq24


@[equational_result]
theorem Equation8502_implies_Equation2 (G : Type*) [Magma G] (h : Equation8502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose eq10 eq7
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))))) = X2 := superpose eq7 eq9
  have eq34 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq20
  have eq44 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X3 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)))) ◇ X0) = X2 := superpose eq7 eq34
  have eq48 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq34 eq10
  have eq49 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ (((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)))) = X3 := superpose eq34 eq9
  have eq50 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X1 := superpose eq34 eq10
  have eq52 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X3 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)))) = ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)))) := superpose eq34 eq9
  have eq61 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) = X3 := superpose eq34 eq49
  have eq64 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)))) ◇ X0) = X2 := superpose eq52 eq44
  have eq83 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq15 eq34
  have eq95 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose eq34 eq83
  have eq116 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq95 eq48
  have eq117 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq95 eq50
  have eq124 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ X0) = X2 := superpose eq95 eq64
  have eq139 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq116 eq117
  have eq140 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq139 eq95
  have eq142 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) = X3 := superpose eq140 eq61
  have eq158 (X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X3 := superpose eq140 eq142
  have eq183 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq158 eq124
  have eq212 (X0 X2 : G) : X0 = X2 := superpose eq183 eq183
  have eq217 (X0 : G) : sK0 ≠ X0 := superpose eq212 eq8
  subsumption eq217 eq212


@[equational_result]
theorem Equation8504_implies_Equation2 (G : Type*) [Magma G] (h : Equation8504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = X0 := superpose eq10 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation8508_implies_Equation2 (G : Type*) [Magma G] (h : Equation8508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X1) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X2)) = X0 := superpose eq10 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation8510_implies_Equation2 (G : Type*) [Magma G] (h : Equation8510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X1) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq19 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq15 eq14
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq10 eq19
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq33 eq24


@[equational_result]
theorem Equation8511_implies_Equation2 (G : Type*) [Magma G] (h : Equation8511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq10
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation8512_implies_Equation2 (G : Type*) [Magma G] (h : Equation8512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X1) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ X4))) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq11 eq11
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq149 eq54


@[equational_result]
theorem Equation8513_implies_Equation2 (G : Type*) [Magma G] (h : Equation8513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X1) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8516_implies_Equation2 (G : Type*) [Magma G] (h : Equation8516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (((X3 ◇ X3) ◇ X0) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq36 eq22


@[equational_result]
theorem Equation8517_implies_Equation2 (G : Type*) [Magma G] (h : Equation8517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq51 eq24


@[equational_result]
theorem Equation8521_implies_Equation2 (G : Type*) [Magma G] (h : Equation8521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3)) ◇ (X4 ◇ (X0 ◇ X5))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3)) ◇ X0) = X4 := superpose eq10 eq9
  have eq14 (X0 X1 X2 X4 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = X4 := superpose eq10 eq12
  have eq15 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq10 eq14
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8524_implies_Equation2 (G : Type*) [Magma G] (h : Equation8524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (((X3 ◇ X3) ◇ X3) ◇ X3))) ◇ (X0 ◇ (((X3 ◇ X3) ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X2)) = X0 := superpose eq13 eq7
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation8525_implies_Equation2 (G : Type*) [Magma G] (h : Equation8525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (((X3 ◇ X3) ◇ X3) ◇ X4))) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8527_implies_Equation2 (G : Type*) [Magma G] (h : Equation8527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq9 eq15
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq30 eq26


@[equational_result]
theorem Equation8528_implies_Equation2 (G : Type*) [Magma G] (h : Equation8528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X5) ◇ (X0 ◇ (((X3 ◇ X3) ◇ X4) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X3)) = X0 := superpose eq13 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation8529_implies_Equation2 (G : Type*) [Magma G] (h : Equation8529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (((X4 ◇ X4) ◇ X5) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X3)) = X0 := superpose eq13 eq7
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq30 eq23


@[equational_result]
theorem Equation8530_implies_Equation2 (G : Type*) [Magma G] (h : Equation8530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X2) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8532_implies_Equation2 (G : Type*) [Magma G] (h : Equation8532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X4 ◇ X5))) = (X1 ◇ ((X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ (X4 ◇ X5))) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ X4) ◇ X5))) ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq7 eq7
  have eq38 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq11
  have eq48 (X0 X4 : G) : ((X0 ◇ X4) ◇ (X4 ◇ X4)) = X4 := superpose eq7 eq38
  have eq75 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ ((X3 ◇ X4) ◇ X0)) = X0 := superpose eq12 eq12
  have eq123 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ X0) = (((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X4) ◇ (X5 ◇ X0)))) ◇ X0) := superpose eq48 eq11
  have eq160 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X4 ◇ X5))) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X4 ◇ X5))) ◇ X0)) := superpose eq48 eq10
  have eq182 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ ((X6 ◇ X7) ◇ X5)) = ((X5 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)))) ◇ ((X0 ◇ ((X6 ◇ X7) ◇ X5)) ◇ X5)) := superpose eq10 eq11
  have eq191 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X4 ◇ X5))) = X0 := superpose eq75 eq160
  have eq198 (X0 X5 : G) : (X5 ◇ X0) = (X0 ◇ X0) := superpose eq191 eq123
  have eq216 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ ((X6 ◇ X7) ◇ X5)) = ((X5 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)))) ◇ (X5 ◇ X5)) := superpose eq198 eq182
  have eq219 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq48 eq198
  have eq257 (X0 X5 X6 X7 : G) : (X0 ◇ ((X6 ◇ X7) ◇ X5)) = X5 := superpose eq219 eq216
  have eq259 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq257 eq7
  have eq288 (X0 X1 : G) : X0 = X1 := superpose eq48 eq259
  have eq310 (X0 : G) : sK0 ≠ X0 := superpose eq288 eq8
  subsumption eq310 eq288


@[equational_result]
theorem Equation8533_implies_Equation2 (G : Type*) [Magma G] (h : Equation8533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq50 eq23


@[equational_result]
theorem Equation8534_implies_Equation2 (G : Type*) [Magma G] (h : Equation8534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (((X4 ◇ X5) ◇ X0) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq36 eq22


@[equational_result]
theorem Equation8535_implies_Equation2 (G : Type*) [Magma G] (h : Equation8535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq51 eq24


@[equational_result]
theorem Equation8537_implies_Equation2 (G : Type*) [Magma G] (h : Equation8537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4))) ◇ (X5 ◇ (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)))))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X4) ◇ X4) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X4) ◇ X4))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq9 eq9
  have eq50 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq15 eq7
  have eq66 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X0 ◇ ((X4 ◇ X5) ◇ (((X2 ◇ X3) ◇ X0) ◇ X0)))) ◇ (X6 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X4 ◇ X5) ◇ (((X2 ◇ X3) ◇ X0) ◇ X0))))))) = X6 := superpose eq11 eq10
  have eq101 (X1 X4 X5 X6 : G) : ((X1 ◇ (X4 ◇ X5)) ◇ (X6 ◇ (X1 ◇ (X1 ◇ (X4 ◇ X5))))) = X6 := superpose eq7 eq66
  have eq108 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) = ((X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq15 eq50
  have eq132 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ (X4 ◇ X5))))) ◇ (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ (X4 ◇ X5))))) = ((X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ (X4 ◇ X5))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ (X4 ◇ X5))))) ◇ (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ (X4 ◇ X5)))))) := superpose eq50 eq10
  have eq135 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq9 eq108
  have eq165 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ (X4 ◇ X5))))) = ((X0 ◇ (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ (X4 ◇ X5))))) ◇ (X1 ◇ (X1 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X5)) ◇ (X4 ◇ X5))))) := superpose eq101 eq132
  have eq166 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq135 eq165
  have eq167 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq166 eq9
  have eq194 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq167 eq167
  have eq195 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq194 eq166
  have eq203 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq195 eq167
  have eq213 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq195 eq203
  have eq218 (X0 X2 : G) : X0 = X2 := superpose eq213 eq213
  have eq220 (X0 : G) : sK0 ≠ X0 := superpose eq218 eq8
  subsumption eq220 eq218


@[equational_result]
theorem Equation8538_implies_Equation2 (G : Type*) [Magma G] (h : Equation8538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X1)) = X0 := superpose eq14 eq7
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq24 eq24
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq34 eq31


@[equational_result]
theorem Equation8539_implies_Equation2 (G : Type*) [Magma G] (h : Equation8539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (((X4 ◇ X5) ◇ X3) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) ◇ (X4 ◇ X5)) ◇ (X6 ◇ (X0 ◇ X5))) = X6 := superpose eq11 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq51 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (((X2 ◇ X3) ◇ X0) ◇ X3)) ◇ (X4 ◇ X5)) ◇ X0) = X6 := superpose eq35 eq22
  have eq69 (X0 X4 X6 : G) : (X4 ◇ X0) = X6 := superpose eq35 eq51
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq69 eq69
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq78 eq70


@[equational_result]
theorem Equation8540_implies_Equation2 (G : Type*) [Magma G] (h : Equation8540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5)) ◇ (X6 ◇ (X0 ◇ X7))) = X6 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5)) ◇ X0) = X6 := superpose eq11 eq10
  have eq16 (X0 X1 X2 X3 X4 X6 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X6 := superpose eq11 eq13
  have eq17 (X0 X3 X6 : G) : (X3 ◇ X0) = X6 := superpose eq11 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq26 eq18


@[equational_result]
theorem Equation8542_implies_Equation2 (G : Type*) [Magma G] (h : Equation8542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X2) ◇ X4) ◇ ((X0 ◇ X1) ◇ X0)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1)) = X4 := superpose eq9 eq9
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X2 ◇ X3) ◇ X2) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq11
  have eq46 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq17 eq34
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq46
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq108 eq47


@[equational_result]
theorem Equation8543_implies_Equation2 (G : Type*) [Magma G] (h : Equation8543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (((X3 ◇ X4) ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X2)) = X0 := superpose eq13 eq7
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq30 eq23


@[equational_result]
theorem Equation8544_implies_Equation2 (G : Type*) [Magma G] (h : Equation8544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ (((X4 ◇ X5) ◇ X4) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X2)) = X0 := superpose eq13 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation8545_implies_Equation2 (G : Type*) [Magma G] (h : Equation8545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8547_implies_Equation2 (G : Type*) [Magma G] (h : Equation8547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X4) ◇ X4))) ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X3) ◇ X4) ◇ ((X0 ◇ X1) ◇ X1)) = X4 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq11 eq7
  have eq27 (X0 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X0)) = X5 := superpose eq25 eq10
  have eq32 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq27
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ (X4 ◇ X5)) ◇ X0) = X3 := superpose eq7 eq27
  have eq57 (X0 X3 X4 : G) : (X4 ◇ X0) = X3 := superpose eq32 eq35
  have eq58 (X0 X5 : G) : X0 = X5 := superpose eq11 eq57
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq87 eq58


@[equational_result]
theorem Equation8548_implies_Equation2 (G : Type*) [Magma G] (h : Equation8548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (((X4 ◇ X5) ◇ X5) ◇ X4))) ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8549_implies_Equation2 (G : Type*) [Magma G] (h : Equation8549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (((X4 ◇ X5) ◇ X5) ◇ X5))) ◇ (X0 ◇ (((X4 ◇ X5) ◇ X5) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X3)) = X0 := superpose eq13 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation8550_implies_Equation2 (G : Type*) [Magma G] (h : Equation8550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (((X4 ◇ X5) ◇ X5) ◇ X6))) ◇ X7))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8552_implies_Equation2 (G : Type*) [Magma G] (h : Equation8552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X7) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq22 (X1 X2 X7 : G) : (X1 ◇ (X2 ◇ X7)) = X2 := superpose eq16 eq9
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq22 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation8553_implies_Equation2 (G : Type*) [Magma G] (h : Equation8553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8554_implies_Equation2 (G : Type*) [Magma G] (h : Equation8554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X7) ◇ (X0 ◇ (((X4 ◇ X5) ◇ X6) ◇ X5))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X4)) = X0 := superpose eq13 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq14 eq14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation8555_implies_Equation2 (G : Type*) [Magma G] (h : Equation8555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (((X5 ◇ X6) ◇ X7) ◇ X7))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X4)) = X0 := superpose eq13 eq7
  have eq23 (X0 X5 : G) : X0 = X5 := superpose eq14 eq14
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq30 eq23


@[equational_result]
theorem Equation8556_implies_Equation2 (G : Type*) [Magma G] (h : Equation8556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X9 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X9))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation8559_implies_Equation2 (G : Type*) [Magma G] (h : Equation8559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq9 eq9
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq23 eq14


@[equational_result]
theorem Equation8562_implies_Equation2 (G : Type*) [Magma G] (h : Equation8562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation8564_implies_Equation2 (G : Type*) [Magma G] (h : Equation8564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq42 eq15


@[equational_result]
theorem Equation8566_implies_Equation2 (G : Type*) [Magma G] (h : Equation8566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq33 eq15


@[equational_result]
theorem Equation8569_implies_Equation2 (G : Type*) [Magma G] (h : Equation8569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation8572_implies_Equation2 (G : Type*) [Magma G] (h : Equation8572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq47 eq14


@[equational_result]
theorem Equation8574_implies_Equation2 (G : Type*) [Magma G] (h : Equation8574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation8576_implies_Equation2 (G : Type*) [Magma G] (h : Equation8576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation8578_implies_Equation2 (G : Type*) [Magma G] (h : Equation8578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (((X0 ◇ X3) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) ◇ ((((X1 ◇ X2) ◇ X1) ◇ (((X0 ◇ X3) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq9 eq9
  have eq33 (X0 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := superpose eq9 eq12
  have eq35 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ (((X0 ◇ X3) ◇ X0) ◇ X2)) ◇ X1))) = (X4 ◇ (X0 ◇ X4)) := superpose eq7 eq12
  have eq67 (X0 X1 X2 X4 : G) : (X1 ◇ X2) = (X4 ◇ (X0 ◇ X4)) := superpose eq33 eq35
  have eq155 (X0 X1 X2 X4 : G) : (X2 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) = X4 := superpose eq67 eq9
  have eq204 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq33 eq155
  have eq256 (X0 X4 : G) : X0 = X4 := superpose eq10 eq204
  have eq466 (X0 : G) : sK0 ≠ X0 := superpose eq256 eq8
  subsumption eq466 eq256


@[equational_result]
theorem Equation8580_implies_Equation2 (G : Type*) [Magma G] (h : Equation8580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation8582_implies_Equation2 (G : Type*) [Magma G] (h : Equation8582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation8584_implies_Equation2 (G : Type*) [Magma G] (h : Equation8584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq57 eq15


@[equational_result]
theorem Equation8588_implies_Equation2 (G : Type*) [Magma G] (h : Equation8588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation8590_implies_Equation2 (G : Type*) [Magma G] (h : Equation8590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation8591_implies_Equation2 (G : Type*) [Magma G] (h : Equation8591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation8592_implies_Equation2 (G : Type*) [Magma G] (h : Equation8592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation8593_implies_Equation2 (G : Type*) [Magma G] (h : Equation8593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq34 eq16


@[equational_result]
theorem Equation8596_implies_Equation2 (G : Type*) [Magma G] (h : Equation8596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation8599_implies_Equation2 (G : Type*) [Magma G] (h : Equation8599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq63 eq14


@[equational_result]
theorem Equation8601_implies_Equation2 (G : Type*) [Magma G] (h : Equation8601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq65 eq15


@[equational_result]
theorem Equation8603_implies_Equation2 (G : Type*) [Magma G] (h : Equation8603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation8606_implies_Equation2 (G : Type*) [Magma G] (h : Equation8606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq62 eq14


@[equational_result]
theorem Equation8608_implies_Equation2 (G : Type*) [Magma G] (h : Equation8608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation8609_implies_Equation2 (G : Type*) [Magma G] (h : Equation8609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8611_implies_Equation2 (G : Type*) [Magma G] (h : Equation8611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8612_implies_Equation2 (G : Type*) [Magma G] (h : Equation8612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8613_implies_Equation2 (G : Type*) [Magma G] (h : Equation8613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8615_implies_Equation2 (G : Type*) [Magma G] (h : Equation8615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X3) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 : G) : (((((X0 ◇ X2) ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((((X0 ◇ X2) ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := superpose eq10 eq9
  have eq28 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) := superpose eq10 eq7
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq10 eq7
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ X2) ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq9 eq28
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := superpose eq34 eq27
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq29 eq36
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq38 eq38
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq83 eq45


@[equational_result]
theorem Equation8617_implies_Equation2 (G : Type*) [Magma G] (h : Equation8617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation8619_implies_Equation2 (G : Type*) [Magma G] (h : Equation8619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8620_implies_Equation2 (G : Type*) [Magma G] (h : Equation8620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8621_implies_Equation2 (G : Type*) [Magma G] (h : Equation8621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8623_implies_Equation2 (G : Type*) [Magma G] (h : Equation8623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8624_implies_Equation2 (G : Type*) [Magma G] (h : Equation8624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8625_implies_Equation2 (G : Type*) [Magma G] (h : Equation8625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8627_implies_Equation2 (G : Type*) [Magma G] (h : Equation8627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8628_implies_Equation2 (G : Type*) [Magma G] (h : Equation8628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8629_implies_Equation2 (G : Type*) [Magma G] (h : Equation8629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8630_implies_Equation2 (G : Type*) [Magma G] (h : Equation8630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation8632_implies_Equation2 (G : Type*) [Magma G] (h : Equation8632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X2)) = (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X2))) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) ◇ ((((X1 ◇ X2) ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = (X2 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq7 eq9
  have eq43 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq15 eq7
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq15 eq10
  have eq64 (X1 X2 : G) : (X2 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq7 eq44
  have eq115 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq15 eq43
  have eq133 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ X1) := superpose eq43 eq115
  have eq134 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq133 eq15
  have eq235 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq134 eq43
  have eq263 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq43 eq235
  have eq264 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := superpose eq263 eq7
  have eq279 (X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X2))) = X2 := superpose eq263 eq64
  have eq356 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq279 eq43
  have eq362 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = X0 := superpose eq356 eq264
  have eq367 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq356 eq362
  have eq405 (X0 X2 : G) : X0 = X2 := superpose eq367 eq367
  have eq407 (X0 : G) : sK0 ≠ X0 := superpose eq405 eq8
  subsumption eq407 eq405


@[equational_result]
theorem Equation8634_implies_Equation2 (G : Type*) [Magma G] (h : Equation8634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation8636_implies_Equation2 (G : Type*) [Magma G] (h : Equation8636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (((X3 ◇ X0) ◇ X2) ◇ X2)) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))))) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (((X3 ◇ (X4 ◇ X1)) ◇ X2) ◇ X2)) = (X5 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq9 eq9
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X1) ◇ X1)) = X0 := superpose eq7 eq9
  have eq32 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq22 eq21
  have eq47 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq10
  have eq58 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq22 eq47
  have eq63 (X0 X1 X5 : G) : (X5 ◇ X0) = X1 := superpose eq58 eq32
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq7 eq63
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq143 eq67


@[equational_result]
theorem Equation8638_implies_Equation2 (G : Type*) [Magma G] (h : Equation8638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation8640_implies_Equation2 (G : Type*) [Magma G] (h : Equation8640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (((X3 ◇ X0) ◇ X3) ◇ X2)) = (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X5 ◇ (((((X4 ◇ X1) ◇ X4) ◇ X2) ◇ X3) ◇ X5))) = (X3 ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) ◇ X3)) := superpose eq9 eq9
  have eq17 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = (X4 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X4))) := superpose eq9 eq9
  have eq24 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (((X4 ◇ (X3 ◇ X1)) ◇ X4) ◇ X3)) = (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1)) = X0 := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ X1) ◇ X4) ◇ X2) = (X3 ◇ (X3 ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) ◇ X3))) := superpose eq9 eq7
  have eq33 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) = X1 := superpose eq25 eq24
  have eq53 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq25
  have eq111 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) ◇ X2) = X0 := superpose eq25 eq53
  have eq112 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X3 ◇ X1) ◇ X3) ◇ X2) := superpose eq53 eq53
  have eq165 (X0 X1 X4 : G) : (X4 ◇ (X4 ◇ (X0 ◇ X4))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq17
  have eq466 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2) ◇ X3) := superpose eq165 eq111
  have eq467 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X1) = X1 := superpose eq165 eq111
  have eq825 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ X3) = (X4 ◇ (X4 ◇ (((X5 ◇ (X5 ◇ (((X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) ◇ X5))) ◇ X3) ◇ X4))) := superpose eq33 eq28
  have eq920 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1))) ◇ (X3 ◇ X2)) ◇ X0))) ◇ X4))) = X3 := superpose eq28 eq7
  have eq1868 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X1 ◇ ((((X0 ◇ X2) ◇ X4) ◇ X5) ◇ X1))) = (X5 ◇ (((X6 ◇ (X6 ◇ (((X3 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X4) ◇ X6))) ◇ X4) ◇ X5)) := superpose eq33 eq13
  have eq1901 (X0 X1 X2 X3 X4 X6 X7 : G) : (X6 ◇ (((X7 ◇ (X7 ◇ ((X2 ◇ X3) ◇ X7))) ◇ X3) ◇ X6)) = (X4 ◇ (X4 ◇ (((X0 ◇ (X0 ◇ (((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X3) ◇ X0))) ◇ X6) ◇ X4))) := superpose eq28 eq13
  have eq1928 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X4 ◇ ((X0 ◇ (X0 ◇ (((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X3) ◇ X0))) ◇ X4))) = (X3 ◇ (((X6 ◇ (X6 ◇ ((X5 ◇ (X2 ◇ X5)) ◇ X6))) ◇ (X2 ◇ X5)) ◇ X3)) := superpose eq28 eq13
  have eq2316 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) = ((X3 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X4)))) ◇ X3) := superpose eq466 eq33
  have eq2337 (X0 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X4)))) ◇ X3) = X0 := superpose eq33 eq2316
  have eq2460 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X4) = ((X3 ◇ (X2 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)))) ◇ X3) := superpose eq112 eq2337
  have eq2519 (X1 X3 X4 : G) : ((X4 ◇ X1) ◇ X4) = ((X3 ◇ X1) ◇ X3) := superpose eq7 eq2460
  have eq2873 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq2519 eq7
  have eq4855 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq2873 eq111
  have eq5281 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq4855 eq2519
  have eq6510 (X0 X1 : G) : ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq5281 eq467
  have eq7073 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) := superpose eq6510 eq2519
  have eq7077 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq25 eq7073
  have eq7078 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq7077 eq7
  have eq10072 (X1 X2 X3 X4 X6 X7 : G) : (X6 ◇ (((X7 ◇ (X7 ◇ ((X2 ◇ X3) ◇ X7))) ◇ X3) ◇ X6)) = (X4 ◇ (X4 ◇ ((((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X3) ◇ X6) ◇ X4))) := superpose eq7078 eq1901
  have eq10073 (X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (((X6 ◇ (X6 ◇ ((X5 ◇ (X2 ◇ X5)) ◇ X6))) ◇ (X2 ◇ X5)) ◇ X3)) = (X4 ◇ (X4 ◇ (((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ X3) ◇ X4))) := superpose eq7078 eq1928
  have eq10076 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ ((((X0 ◇ X2) ◇ X4) ◇ X5) ◇ X1))) = (X5 ◇ ((((X3 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X4) ◇ X4) ◇ X5)) := superpose eq7078 eq1868
  have eq10077 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X3) = (X4 ◇ (X4 ◇ ((((X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) ◇ X3) ◇ X4))) := superpose eq7078 eq825
  have eq10079 (X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ (((X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1))) ◇ (X3 ◇ X2)) ◇ X4))) = X3 := superpose eq7078 eq920
  have eq10119 (X2 X3 X4 X6 X7 : G) : (X6 ◇ (((X7 ◇ (X7 ◇ ((X2 ◇ X3) ◇ X7))) ◇ X3) ◇ X6)) = (X4 ◇ (X4 ◇ ((((X2 ◇ X3) ◇ X3) ◇ X6) ◇ X4))) := superpose eq7078 eq10072
  have eq10120 (X2 X3 X6 X7 : G) : (X6 ◇ (((X7 ◇ (X7 ◇ ((X2 ◇ X3) ◇ X7))) ◇ X3) ◇ X6)) = (((X2 ◇ X3) ◇ X3) ◇ X6) := superpose eq7078 eq10119
  have eq10121 (X2 X3 X6 : G) : (((X2 ◇ X3) ◇ X3) ◇ X6) = (X6 ◇ (((X2 ◇ X3) ◇ X3) ◇ X6)) := superpose eq7078 eq10120
  have eq10122 (X2 X3 X4 X5 X6 : G) : (X3 ◇ (((X6 ◇ (X6 ◇ ((X5 ◇ (X2 ◇ X5)) ◇ X6))) ◇ (X2 ◇ X5)) ◇ X3)) = (X4 ◇ (X4 ◇ (((X2 ◇ X3) ◇ X3) ◇ X4))) := superpose eq7078 eq10073
  have eq10123 (X2 X3 X5 X6 : G) : ((X2 ◇ X3) ◇ X3) = (X3 ◇ (((X6 ◇ (X6 ◇ ((X5 ◇ (X2 ◇ X5)) ◇ X6))) ◇ (X2 ◇ X5)) ◇ X3)) := superpose eq7078 eq10122
  have eq10124 (X2 X3 X5 : G) : ((X2 ◇ X3) ◇ X3) = (X3 ◇ (((X5 ◇ (X2 ◇ X5)) ◇ (X2 ◇ X5)) ◇ X3)) := superpose eq7078 eq10123
  have eq10129 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X1 ◇ ((((X0 ◇ X2) ◇ X4) ◇ X5) ◇ X1))) = (X5 ◇ ((((X0 ◇ X2) ◇ X4) ◇ X4) ◇ X5)) := superpose eq7078 eq10076
  have eq10130 (X0 X2 X4 X5 : G) : (((X0 ◇ X2) ◇ X4) ◇ X5) = (X5 ◇ ((((X0 ◇ X2) ◇ X4) ◇ X4) ◇ X5)) := superpose eq7078 eq10129
  have eq10131 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X3) = (X4 ◇ ((((X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X3) ◇ X3) ◇ X4)) := superpose eq10121 eq10077
  have eq10132 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ X3) = (X4 ◇ ((((X0 ◇ X1) ◇ X3) ◇ X3) ◇ X4)) := superpose eq7078 eq10131
  have eq10133 (X0 X2 X4 X5 : G) : ((X0 ◇ X2) ◇ X4) = (((X0 ◇ X2) ◇ X4) ◇ X5) := superpose eq10132 eq10130
  have eq10134 (X2 X3 X6 : G) : ((X2 ◇ X3) ◇ X3) = (X6 ◇ ((X2 ◇ X3) ◇ X3)) := superpose eq10133 eq10121
  have eq10135 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ X3) = (X4 ◇ (((X0 ◇ X1) ◇ X3) ◇ X4)) := superpose eq10133 eq10132
  have eq10136 (X2 X3 X5 : G) : ((X2 ◇ X3) ◇ X3) = (X3 ◇ ((X5 ◇ (X2 ◇ X5)) ◇ (X2 ◇ X5))) := superpose eq10133 eq10124
  have eq10139 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ X3) = (X4 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq10133 eq10135
  have eq10149 (X1 X2 X3 X4 : G) : (X4 ◇ (((X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1))) ◇ (X3 ◇ X2)) ◇ X4)) = X3 := superpose eq10139 eq10079
  have eq10150 (X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1))) ◇ (X3 ◇ X2))) = X3 := superpose eq10133 eq10149
  have eq10151 (X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X3 ◇ X2))) = X3 := superpose eq7078 eq10150
  have eq10152 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X2 := superpose eq10151 eq10136
  have eq10154 (X2 X6 : G) : (X6 ◇ X2) = X2 := superpose eq10152 eq10134
  have eq10160 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq10154 eq7078
  have eq10164 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10154 eq10160
  have eq10165 (X0 X2 : G) : X0 = X2 := superpose eq10164 eq10164
  have eq10167 (X0 : G) : sK0 ≠ X0 := superpose eq10165 eq8
  subsumption eq10167 eq10165


@[equational_result]
theorem Equation8642_implies_Equation2 (G : Type*) [Magma G] (h : Equation8642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation8644_implies_Equation2 (G : Type*) [Magma G] (h : Equation8644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation8645_implies_Equation2 (G : Type*) [Magma G] (h : Equation8645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation8646_implies_Equation2 (G : Type*) [Magma G] (h : Equation8646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (((X3 ◇ X0) ◇ X4) ◇ X4)) = (X1 ◇ (X1 ◇ ((X0 ◇ X5) ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X4) ◇ X4)) ◇ X0) = X2 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X0) ◇ (((X2 ◇ (((X3 ◇ X4) ◇ X5) ◇ X5)) ◇ X6) ◇ X6)) ◇ X0) = X4 := superpose eq11 eq7
  have eq45 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X4) ◇ X4)) = X0 := superpose eq7 eq9
  have eq69 (X0 X4 X5 : G) : (X5 ◇ X0) = X4 := superpose eq45 eq22
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq69
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq173 eq71


@[equational_result]
theorem Equation8647_implies_Equation2 (G : Type*) [Magma G] (h : Equation8647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq35 eq17


@[equational_result]
theorem Equation8649_implies_Equation2 (G : Type*) [Magma G] (h : Equation8649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) ◇ ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X3) ◇ (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X1))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X2 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) := superpose eq10 eq7
  have eq18 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq10 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (((((X3 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) ◇ X4) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))))) = X4 := superpose eq10 eq9
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1))) ◇ X0)) = X1 := superpose eq7 eq9
  have eq41 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) = X1 := superpose eq10 eq33
  have eq50 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = ((X2 ◇ (((X3 ◇ (X4 ◇ X0)) ◇ X1) ◇ (X4 ◇ X0))) ◇ ((((X3 ◇ (X4 ◇ X0)) ◇ X1) ◇ (X4 ◇ X0)) ◇ ((((X3 ◇ (X4 ◇ X0)) ◇ X1) ◇ (X4 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq10 eq18
  have eq83 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X1))) := superpose eq10 eq41
  have eq97 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (X1 ◇ (X1 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X1))) := superpose eq18 eq83
  have eq99 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X3 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq97 eq17
  have eq113 (X0 X1 X4 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X4) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))))) = X4 := superpose eq99 eq29
  have eq114 (X0 X1 X2 X4 : G) : (X4 ◇ X0) = ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq99 eq50
  have eq119 (X0 X4 : G) : (X4 ◇ X0) = X0 := superpose eq18 eq114
  have eq121 (X0 X1 X4 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X4) ◇ (X0 ◇ X0)))) = X4 := superpose eq119 eq113
  have eq154 (X0 X1 X4 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X4) ◇ (X0 ◇ X0))) = X4 := superpose eq119 eq121
  have eq155 (X0 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X4 := superpose eq119 eq154
  have eq156 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq119 eq155
  have eq169 (X0 X2 : G) : X0 = X2 := superpose eq156 eq156
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq169 eq8
  subsumption eq171 eq169


@[equational_result]
theorem Equation8651_implies_Equation2 (G : Type*) [Magma G] (h : Equation8651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation8653_implies_Equation2 (G : Type*) [Magma G] (h : Equation8653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8654_implies_Equation2 (G : Type*) [Magma G] (h : Equation8654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8655_implies_Equation2 (G : Type*) [Magma G] (h : Equation8655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8657_implies_Equation2 (G : Type*) [Magma G] (h : Equation8657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8658_implies_Equation2 (G : Type*) [Magma G] (h : Equation8658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation8659_implies_Equation2 (G : Type*) [Magma G] (h : Equation8659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8661_implies_Equation2 (G : Type*) [Magma G] (h : Equation8661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation8662_implies_Equation2 (G : Type*) [Magma G] (h : Equation8662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


