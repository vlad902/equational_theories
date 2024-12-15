import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation21917_implies_Equation2 (G : Type*) [Magma G] (h : Equation21917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ X3) = (X0 ◇ (X4 ◇ ((X0 ◇ X3) ◇ X4))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq7 eq12
  have eq42 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X3 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq23 eq23
  have eq52 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X2)) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X2 := superpose eq23 eq7
  have eq65 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq42
  have eq115 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1))) = X0 := superpose eq10 eq65
  have eq118 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq12 eq65
  have eq143 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X0 := superpose eq65 eq118
  have eq150 (X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X2)) ◇ X1) = X2 := superpose eq143 eq52
  have eq170 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq150 eq115
  have eq330 (X0 X1 : G) : X0 = X1 := superpose eq7 eq170
  have eq449 (X0 : G) : sK0 ≠ X0 := superpose eq330 eq8
  subsumption eq449 eq330


@[equational_result]
theorem Equation21918_implies_Equation2 (G : Type*) [Magma G] (h : Equation21918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq12 eq12
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq7 eq17
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq129 eq39


@[equational_result]
theorem Equation21920_implies_Equation2 (G : Type*) [Magma G] (h : Equation21920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq12
  have eq24 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X2 := superpose eq13 eq11
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq24
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation21921_implies_Equation2 (G : Type*) [Magma G] (h : Equation21921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X4)) ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X5 X6 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X6) = X5 := superpose eq7 eq12
  have eq23 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X5 ◇ X0)) = X4 := superpose eq13 eq11
  have eq25 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X4 := superpose eq13 eq23
  have eq30 (X0 X5 : G) : X0 = X5 := superpose eq12 eq25
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq50 eq30


@[equational_result]
theorem Equation21922_implies_Equation2 (G : Type*) [Magma G] (h : Equation21922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = (X0 ◇ (X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X4))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq12 eq12
  have eq23 (X0 X1 X3 X4 : G) : (X1 ◇ X3) = (X0 ◇ (X4 ◇ X0)) := superpose eq14 eq10
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq23
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq152 eq53


@[equational_result]
theorem Equation21923_implies_Equation2 (G : Type*) [Magma G] (h : Equation21923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X4 := superpose eq12 eq11
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation21925_implies_Equation2 (G : Type*) [Magma G] (h : Equation21925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4)) ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 X6 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X6) = X5 := superpose eq7 eq12
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X5 ◇ X0)) = X4 := superpose eq13 eq11
  have eq25 (X0 X3 X4 X5 : G) : (X3 ◇ (X5 ◇ X0)) = X4 := superpose eq13 eq23
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq52 eq30


@[equational_result]
theorem Equation21926_implies_Equation2 (G : Type*) [Magma G] (h : Equation21926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X2) = (X0 ◇ (X4 ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq7 eq22
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq143 eq59


@[equational_result]
theorem Equation21927_implies_Equation2 (G : Type*) [Magma G] (h : Equation21927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X3) = (X0 ◇ (X4 ◇ (X3 ◇ X4))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq172 eq55


@[equational_result]
theorem Equation21928_implies_Equation2 (G : Type*) [Magma G] (h : Equation21928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ X0)) = X4 := superpose eq12 eq11
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq51 eq31


@[equational_result]
theorem Equation21930_implies_Equation2 (G : Type*) [Magma G] (h : Equation21930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X4 ◇ (X4 ◇ X2)) = ((X1 ◇ X0) ◇ (X5 ◇ (X5 ◇ X1))) := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq9
  have eq107 (X0 X3 : G) : X0 = X3 := superpose eq7 eq28
  have eq195 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq195 eq107


@[equational_result]
theorem Equation21931_implies_Equation2 (G : Type*) [Magma G] (h : Equation21931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = (X0 ◇ (X4 ◇ (X4 ◇ X3))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq184 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq184 eq61


@[equational_result]
theorem Equation21932_implies_Equation2 (G : Type*) [Magma G] (h : Equation21932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X3 ◇ X3) = (X0 ◇ (X4 ◇ (X4 ◇ X4))) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq60 (X0 X1 : G) : X0 = X1 := superpose eq7 eq18
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq134 eq60


@[equational_result]
theorem Equation21933_implies_Equation2 (G : Type*) [Magma G] (h : Equation21933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq12 eq12
  have eq54 (X0 X5 : G) : X0 = X5 := superpose eq7 eq17
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq158 eq54


@[equational_result]
theorem Equation21935_implies_Equation2 (G : Type*) [Magma G] (h : Equation21935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ (X6 ◇ X0)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : ((X0 ◇ (X5 ◇ X6)) ◇ X7) = X6 := superpose eq7 eq12
  have eq23 (X0 X3 X5 X6 : G) : (X3 ◇ (X6 ◇ X0)) = X5 := superpose eq13 eq11
  have eq28 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq50 eq28


@[equational_result]
theorem Equation21936_implies_Equation2 (G : Type*) [Magma G] (h : Equation21936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X4 ◇ X2) = (X0 ◇ (X5 ◇ (X6 ◇ X3))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq22
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq140 eq57


@[equational_result]
theorem Equation21937_implies_Equation2 (G : Type*) [Magma G] (h : Equation21937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq12 eq12
  have eq54 (X0 X5 : G) : X0 = X5 := superpose eq7 eq17
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq158 eq54


@[equational_result]
theorem Equation21938_implies_Equation2 (G : Type*) [Magma G] (h : Equation21938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq12 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation21939_implies_Equation2 (G : Type*) [Magma G] (h : Equation21939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq12 eq12
  have eq53 (X0 X6 : G) : X0 = X6 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation21941_implies_Equation2 (G : Type*) [Magma G] (h : Equation21941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq7 eq10
  have eq38 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq24
  have eq44 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq7 eq16
  have eq59 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq44
  have eq72 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq11 eq10
  have eq77 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = ((((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X4 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))))) := superpose eq11 eq10
  have eq85 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq7 eq72
  have eq88 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))))) := superpose eq11 eq77
  have eq93 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq10 eq85
  have eq114 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq7 eq14
  have eq129 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = ((((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ ((((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq16 eq14
  have eq165 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq114
  have eq167 (X0 X1 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ (((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq16 eq114
  have eq173 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0)) := superpose eq114 eq16
  have eq174 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0)) := superpose eq114 eq10
  have eq175 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq114 eq9
  have eq176 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0) = X0 := superpose eq114 eq7
  have eq189 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq165
  have eq193 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq176 eq174
  have eq194 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X0 ◇ X0) ◇ X0) := superpose eq176 eq173
  have eq195 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq194 eq193
  have eq196 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq194 eq176
  have eq199 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq195 eq189
  have eq202 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq195 eq38
  have eq203 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq195 eq59
  have eq205 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq195 eq85
  have eq206 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X3 ◇ ((X0 ◇ X0) ◇ X0))))) := superpose eq195 eq88
  have eq217 (X0 X1 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq199 eq202
  have eq218 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq199 eq203
  have eq221 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))) = ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq205 eq167
  have eq223 (X0 X1 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq218 eq221
  have eq224 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq199 eq206
  have eq291 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq196 eq205
  have eq301 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq205 eq7
  have eq303 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq205 eq10
  have eq330 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq291 eq205
  have eq346 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq330 eq129
  have eq347 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq330 eq217
  have eq348 (X0 X1 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq330 eq224
  have eq387 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq330 eq223
  have eq401 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X2) ◇ ((((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq330 eq93
  have eq437 (X0 X2 : G) : (((X2 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X2 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq330 eq346
  have eq438 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := superpose eq330 eq347
  have eq439 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ X0) := superpose eq330 eq438
  have eq440 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq330 eq439
  have eq441 (X0 X1 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq330 eq348
  have eq442 (X0 X1 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq330 eq441
  have eq443 (X0 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X4 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq330 eq442
  have eq444 (X0 X4 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X4 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq440 eq443
  have eq445 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq330 eq444
  have eq446 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq440 eq445
  have eq448 (X0 X2 : G) : (((X2 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X2 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq446 eq437
  have eq452 (X0 X2 : G) : (((X2 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((((X2 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq446 eq448
  have eq453 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X2 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq330 eq452
  have eq454 (X0 X2 : G) : (X0 ◇ X0) = (((X2 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq446 eq453
  have eq519 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq330 eq387
  have eq520 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq454 eq519
  have eq521 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq175 eq520
  have eq526 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq521 eq330
  have eq650 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq526 eq401
  have eq651 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ X0) := superpose eq521 eq650
  have eq695 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq526 eq301
  have eq696 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq521 eq695
  have eq697 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq526 eq696
  have eq706 (X0 X1 X3 : G) : (X1 ◇ X0) = (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq526 eq303
  have eq707 (X0 X1 X3 : G) : (X1 ◇ X0) = (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ X0) := superpose eq697 eq706
  have eq708 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq526 eq707
  have eq709 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq526 eq708
  have eq710 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq697 eq709
  have eq711 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq710 eq651
  have eq828 (X0 X1 : G) : X0 = X1 := superpose eq710 eq711
  have eq830 (X0 : G) : sK0 ≠ X0 := superpose eq828 eq8
  subsumption eq830 eq828


@[equational_result]
theorem Equation21943_implies_Equation2 (G : Type*) [Magma G] (h : Equation21943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq22 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq14 eq10
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq22 eq14
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq34 eq29


@[equational_result]
theorem Equation21945_implies_Equation2 (G : Type*) [Magma G] (h : Equation21945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq11 eq11
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X0))) = ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq7
  have eq41 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq7 eq28
  have eq42 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq10 eq28
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq28 eq7
  have eq64 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X3 ◇ X0)) = X3 := superpose eq28 eq10
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq42 eq33
  have eq107 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq62 eq91
  have eq120 (X0 X1 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq42 eq64
  have eq145 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq28 eq9
  have eq153 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq41 eq145
  have eq159 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq107 eq28
  have eq165 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq159 eq7
  have eq169 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq159 eq62
  have eq173 (X0 X3 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq159 eq120
  have eq183 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq159 eq169
  have eq186 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq107 eq173
  have eq202 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq165 eq186
  have eq209 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq202 eq153
  have eq214 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq183 eq209
  have eq217 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq214 eq165
  have eq236 (X0 X2 : G) : X0 = X2 := superpose eq217 eq217
  have eq246 (X0 : G) : sK0 ≠ X0 := superpose eq236 eq8
  subsumption eq246 eq236


@[equational_result]
theorem Equation21947_implies_Equation2 (G : Type*) [Magma G] (h : Equation21947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = X0 := superpose eq13 eq7
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq13 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation21949_implies_Equation2 (G : Type*) [Magma G] (h : Equation21949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq9
  have eq21 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X4 ◇ X0)) ◇ X4) := superpose eq9 eq10
  have eq37 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq11 eq11
  have eq78 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X1 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq21 eq7
  have eq107 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq10 eq78
  have eq108 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X1 := superpose eq7 eq107
  have eq115 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X4 := superpose eq108 eq11
  have eq144 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq115 eq37
  have eq151 (X0 X2 : G) : X0 = X2 := superpose eq144 eq144
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq151 eq8
  subsumption eq162 eq151


@[equational_result]
theorem Equation21951_implies_Equation2 (G : Type*) [Magma G] (h : Equation21951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq20 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq14 eq10
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation21953_implies_Equation2 (G : Type*) [Magma G] (h : Equation21953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X4 ◇ X2)) = (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq11
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq150 eq68


@[equational_result]
theorem Equation21954_implies_Equation2 (G : Type*) [Magma G] (h : Equation21954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X3 ◇ X4)) = ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq40 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq11
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq40 eq40
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq168 eq69


@[equational_result]
theorem Equation21955_implies_Equation2 (G : Type*) [Magma G] (h : Equation21955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq10 eq10
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = X0 := superpose eq14 eq7
  have eq26 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq14 eq23
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation21956_implies_Equation2 (G : Type*) [Magma G] (h : Equation21956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq21 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq13 eq10
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation21958_implies_Equation2 (G : Type*) [Magma G] (h : Equation21958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X2 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))))) = X2 := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq10 eq10
  have eq45 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq31
  have eq109 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq45 eq11
  have eq115 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq109
  have eq126 (X0 X2 : G) : X0 = X2 := superpose eq7 eq115
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq126 eq8
  subsumption eq143 eq126


@[equational_result]
theorem Equation21960_implies_Equation2 (G : Type*) [Magma G] (h : Equation21960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := superpose eq19 eq7
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq19 eq25
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq19 eq34
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq67 eq65


@[equational_result]
theorem Equation21962_implies_Equation2 (G : Type*) [Magma G] (h : Equation21962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21963_implies_Equation2 (G : Type*) [Magma G] (h : Equation21963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21964_implies_Equation2 (G : Type*) [Magma G] (h : Equation21964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21966_implies_Equation2 (G : Type*) [Magma G] (h : Equation21966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation21967_implies_Equation2 (G : Type*) [Magma G] (h : Equation21967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21968_implies_Equation2 (G : Type*) [Magma G] (h : Equation21968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21970_implies_Equation2 (G : Type*) [Magma G] (h : Equation21970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21971_implies_Equation2 (G : Type*) [Magma G] (h : Equation21971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21972_implies_Equation2 (G : Type*) [Magma G] (h : Equation21972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21973_implies_Equation2 (G : Type*) [Magma G] (h : Equation21973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21976_implies_Equation2 (G : Type*) [Magma G] (h : Equation21976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := superpose eq10 eq10
  have eq43 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2))) = X1 := superpose eq10 eq7
  have eq45 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (((X3 ◇ (X4 ◇ X3)) ◇ X4) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)))) := superpose eq10 eq9
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X3) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2))) ◇ X3) ◇ ((X4 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X5 ◇ (X4 ◇ ((X1 ◇ X3) ◇ X4))))) = X5 := superpose eq10 eq9
  have eq50 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (X4 ◇ X3)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2))) = X1 := superpose eq10 eq9
  have eq56 (X1 X3 X4 : G) : (X3 ◇ X1) = (((X3 ◇ (X4 ◇ X3)) ◇ X4) ◇ X1) := superpose eq43 eq45
  have eq113 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ X2)) ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq40 eq9
  have eq140 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X3 ◇ (X1 ◇ X3))) ◇ X2) := superpose eq7 eq56
  have eq174 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq113 eq140
  have eq187 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X2))) = X1 := superpose eq174 eq43
  have eq190 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X3) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X2))) ◇ X3) ◇ ((X4 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X5 ◇ (X4 ◇ ((X1 ◇ X3) ◇ X4))))) = X5 := superpose eq174 eq47
  have eq193 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (X4 ◇ X3)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X2))) = X1 := superpose eq174 eq50
  have eq240 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq174 eq187
  have eq244 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X3) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X2))) ◇ X3) ◇ X4) = X5 := superpose eq240 eq190
  have eq245 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ X4) = X5 := superpose eq174 eq244
  have eq248 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (X4 ◇ X3)) ◇ X4) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq174 eq193
  have eq249 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq174 eq248
  have eq255 (X1 X3 X4 X5 : G) : ((X1 ◇ X3) ◇ X4) = X5 := superpose eq249 eq245
  have eq269 (X0 X3 : G) : X0 = X3 := superpose eq7 eq255
  have eq329 (X0 : G) : sK0 ≠ X0 := superpose eq269 eq8
  subsumption eq329 eq269


@[equational_result]
theorem Equation21977_implies_Equation2 (G : Type*) [Magma G] (h : Equation21977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1)) ◇ X0) = X3 := superpose eq7 eq7
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq43 eq33


@[equational_result]
theorem Equation21979_implies_Equation2 (G : Type*) [Magma G] (h : Equation21979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21980_implies_Equation2 (G : Type*) [Magma G] (h : Equation21980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21981_implies_Equation2 (G : Type*) [Magma G] (h : Equation21981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21983_implies_Equation2 (G : Type*) [Magma G] (h : Equation21983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation21984_implies_Equation2 (G : Type*) [Magma G] (h : Equation21984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21985_implies_Equation2 (G : Type*) [Magma G] (h : Equation21985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21987_implies_Equation2 (G : Type*) [Magma G] (h : Equation21987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21988_implies_Equation2 (G : Type*) [Magma G] (h : Equation21988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation21989_implies_Equation2 (G : Type*) [Magma G] (h : Equation21989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21990_implies_Equation2 (G : Type*) [Magma G] (h : Equation21990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation21992_implies_Equation2 (G : Type*) [Magma G] (h : Equation21992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation21993_implies_Equation2 (G : Type*) [Magma G] (h : Equation21993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation21994_implies_Equation2 (G : Type*) [Magma G] (h : Equation21994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X2))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq130 eq53


@[equational_result]
theorem Equation21995_implies_Equation2 (G : Type*) [Magma G] (h : Equation21995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X5 := superpose eq7 eq7
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation21997_implies_Equation2 (G : Type*) [Magma G] (h : Equation21997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21998_implies_Equation2 (G : Type*) [Magma G] (h : Equation21998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation21999_implies_Equation2 (G : Type*) [Magma G] (h : Equation21999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22000_implies_Equation2 (G : Type*) [Magma G] (h : Equation22000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22002_implies_Equation2 (G : Type*) [Magma G] (h : Equation22002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22003_implies_Equation2 (G : Type*) [Magma G] (h : Equation22003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22004_implies_Equation2 (G : Type*) [Magma G] (h : Equation22004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22005_implies_Equation2 (G : Type*) [Magma G] (h : Equation22005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22007_implies_Equation2 (G : Type*) [Magma G] (h : Equation22007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22008_implies_Equation2 (G : Type*) [Magma G] (h : Equation22008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22009_implies_Equation2 (G : Type*) [Magma G] (h : Equation22009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22010_implies_Equation2 (G : Type*) [Magma G] (h : Equation22010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22012_implies_Equation2 (G : Type*) [Magma G] (h : Equation22012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22013_implies_Equation2 (G : Type*) [Magma G] (h : Equation22013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22014_implies_Equation2 (G : Type*) [Magma G] (h : Equation22014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22015_implies_Equation2 (G : Type*) [Magma G] (h : Equation22015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22016_implies_Equation2 (G : Type*) [Magma G] (h : Equation22016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22018_implies_Equation2 (G : Type*) [Magma G] (h : Equation22018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X3)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq9 eq9
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq36 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) = (((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X4 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq10 eq10
  have eq44 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq13
  have eq51 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq13 eq13
  have eq66 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) = (((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) ◇ (X4 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq44 eq36
  have eq78 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq51 eq17
  have eq79 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3)) = X0 := superpose eq51 eq66
  have eq101 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq78 eq79
  have eq102 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq78 eq101
  have eq103 (X0 X3 : G) : X0 = X3 := superpose eq102 eq102
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq103 eq8
  subsumption eq108 eq103


@[equational_result]
theorem Equation22019_implies_Equation2 (G : Type*) [Magma G] (h : Equation22019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq9 eq9
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq15 eq11
  have eq23 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq19 eq19
  have eq29 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X1))) = ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq19 eq7
  have eq33 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X1))) = ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq19 eq29
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq23 eq33
  have eq35 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq19 eq34
  have eq37 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq35 eq16
  have eq45 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X2 ◇ X0) := superpose eq35 eq37
  have eq46 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq7 eq45
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq46 eq7
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq46 eq47
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq46 eq54
  have eq56 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq46 eq55
  have eq90 (X0 X2 : G) : X0 = X2 := superpose eq56 eq56
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq92 eq90


@[equational_result]
theorem Equation22020_implies_Equation2 (G : Type*) [Magma G] (h : Equation22020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = ((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq9
  have eq29 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq11
  have eq40 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq29
  have eq41 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq29
  have eq44 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X0 := superpose eq29 eq11
  have eq53 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq29 eq40
  have eq60 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq53 eq44
  have eq61 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq60 eq41
  have eq63 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq61 eq12
  have eq67 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq63 eq61
  have eq85 (X0 X1 : G) : X0 = X1 := superpose eq63 eq67
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq106 eq85


@[equational_result]
theorem Equation22022_implies_Equation2 (G : Type*) [Magma G] (h : Equation22022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq11
  have eq31 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq11
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) = ((X0 ◇ X1) ◇ X0) := superpose eq11 eq9
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq11 eq31
  have eq55 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq31 eq31
  have eq58 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq31 eq7
  have eq67 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq55 eq54
  have eq68 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq67 eq37
  have eq73 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq68 eq23
  have eq78 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq58 eq73
  have eq79 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq78 eq12
  have eq82 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq79 eq7
  have eq92 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq79 eq82
  have eq95 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq92 eq31
  have eq104 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq92 eq95
  have eq106 (X0 X1 : G) : X0 = X1 := superpose eq92 eq104
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq120 eq106


@[equational_result]
theorem Equation22024_implies_Equation2 (G : Type*) [Magma G] (h : Equation22024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X4))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq112 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq10
  have eq142 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = X4 := superpose eq112 eq11
  have eq158 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq142 eq142
  have eq164 (X0 X3 : G) : X0 = X3 := superpose eq158 eq158
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq164 eq8
  subsumption eq179 eq164


@[equational_result]
theorem Equation22027_implies_Equation2 (G : Type*) [Magma G] (h : Equation22027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq11
  have eq14 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq13
  have eq15 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq14 eq7
  have eq16 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq14 eq15
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22028_implies_Equation2 (G : Type*) [Magma G] (h : Equation22028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X3)))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq11
  have eq14 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq13
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X2) = X0 := superpose eq14 eq7
  have eq26 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq14 eq22
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq13 eq26
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq36 eq27


@[equational_result]
theorem Equation22030_implies_Equation2 (G : Type*) [Magma G] (h : Equation22030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X1 ◇ (X2 ◇ X2))))) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X2)))) = X4 := superpose eq9 eq9
  have eq23 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq14 eq13
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq156 eq47


@[equational_result]
theorem Equation22031_implies_Equation2 (G : Type*) [Magma G] (h : Equation22031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X3)))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X0))) = X4 := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) = X4 := superpose eq18 eq11
  have eq27 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq22
  have eq44 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq27 eq13
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq44 eq44
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq57 eq49


@[equational_result]
theorem Equation22032_implies_Equation2 (G : Type*) [Magma G] (h : Equation22032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X4 ◇ X4))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X5))) = X4 := superpose eq7 eq9
  have eq28 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq11 eq11
  have eq43 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq28 eq13
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq56 eq44


@[equational_result]
theorem Equation22033_implies_Equation2 (G : Type*) [Magma G] (h : Equation22033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X4 ◇ X5))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X7))) = X5 := superpose eq7 eq9
  have eq28 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq11 eq11
  have eq39 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq28 eq13
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq52 eq44


@[equational_result]
theorem Equation22035_implies_Equation2 (G : Type*) [Magma G] (h : Equation22035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq9 eq9
  have eq32 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq7 eq17
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq9 eq17
  have eq49 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq32 eq7
  have eq58 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq33 eq49
  have eq65 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq33 eq58
  have eq66 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq33 eq65
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq66 eq66
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq69 eq67


@[equational_result]
theorem Equation22036_implies_Equation2 (G : Type*) [Magma G] (h : Equation22036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X0))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = X1 := superpose eq9 eq9
  have eq25 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq21 eq10
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq7 eq25
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq52 eq28


@[equational_result]
theorem Equation22037_implies_Equation2 (G : Type*) [Magma G] (h : Equation22037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X1 := superpose eq9 eq9
  have eq23 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq18 eq10
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22039_implies_Equation2 (G : Type*) [Magma G] (h : Equation22039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22040_implies_Equation2 (G : Type*) [Magma G] (h : Equation22040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22041_implies_Equation2 (G : Type*) [Magma G] (h : Equation22041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22043_implies_Equation2 (G : Type*) [Magma G] (h : Equation22043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22044_implies_Equation2 (G : Type*) [Magma G] (h : Equation22044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation22045_implies_Equation2 (G : Type*) [Magma G] (h : Equation22045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22047_implies_Equation2 (G : Type*) [Magma G] (h : Equation22047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22048_implies_Equation2 (G : Type*) [Magma G] (h : Equation22048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22049_implies_Equation2 (G : Type*) [Magma G] (h : Equation22049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22050_implies_Equation2 (G : Type*) [Magma G] (h : Equation22050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22053_implies_Equation2 (G : Type*) [Magma G] (h : Equation22053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X2)) = ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2)))) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq7 eq9
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq10 eq10
  have eq45 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq27 eq7
  have eq48 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X3 ◇ (((X1 ◇ X1) ◇ (X4 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X4 ◇ (X1 ◇ X1))))) ◇ (((X1 ◇ X1) ◇ (X4 ◇ (X1 ◇ X1))) ◇ X4)) := superpose eq27 eq10
  have eq50 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X3 ◇ (X1 ◇ X1)))) = X3 := superpose eq27 eq7
  have eq51 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X3 ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X4)) := superpose eq27 eq10
  have eq54 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq27 eq9
  have eq71 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X3 ◇ X4) ◇ (((X1 ◇ X1) ◇ (X4 ◇ (X1 ◇ X1))) ◇ X4)) := superpose eq50 eq48
  have eq72 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X3 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X4)) := superpose eq50 eq51
  have eq73 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X2 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq54
  have eq75 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X1))) = ((X3 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X4)) := superpose eq73 eq72
  have eq97 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := superpose eq14 eq14
  have eq131 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := superpose eq73 eq97
  have eq132 (X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := superpose eq73 eq131
  have eq133 (X1 X2 : G) : (X2 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq45 eq132
  have eq139 (X0 X2 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X2 := superpose eq133 eq13
  have eq142 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X4)) = X1 := superpose eq133 eq75
  have eq166 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq142 eq71
  have eq167 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ (X1 ◇ X4)) = X1 := superpose eq166 eq142
  have eq173 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq167 eq139
  have eq174 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq173 eq7
  have eq193 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq173 eq174
  have eq194 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq173 eq193
  have eq195 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq173 eq194
  have eq206 (X0 X2 : G) : X0 = X2 := superpose eq195 eq195
  have eq208 (X0 : G) : sK0 ≠ X0 := superpose eq206 eq8
  subsumption eq208 eq206


@[equational_result]
theorem Equation22054_implies_Equation2 (G : Type*) [Magma G] (h : Equation22054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq10
  have eq22 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X0) = X3 := superpose eq13 eq12
  have eq24 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq22 eq10
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation22056_implies_Equation2 (G : Type*) [Magma G] (h : Equation22056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22057_implies_Equation2 (G : Type*) [Magma G] (h : Equation22057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22058_implies_Equation2 (G : Type*) [Magma G] (h : Equation22058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22060_implies_Equation2 (G : Type*) [Magma G] (h : Equation22060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22061_implies_Equation2 (G : Type*) [Magma G] (h : Equation22061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation22062_implies_Equation2 (G : Type*) [Magma G] (h : Equation22062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22064_implies_Equation2 (G : Type*) [Magma G] (h : Equation22064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22065_implies_Equation2 (G : Type*) [Magma G] (h : Equation22065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22066_implies_Equation2 (G : Type*) [Magma G] (h : Equation22066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22067_implies_Equation2 (G : Type*) [Magma G] (h : Equation22067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22069_implies_Equation2 (G : Type*) [Magma G] (h : Equation22069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X2)))) = X5 := superpose eq9 eq9
  have eq23 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq14 eq10
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22070_implies_Equation2 (G : Type*) [Magma G] (h : Equation22070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq10 eq10
  have eq24 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq14 eq10
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq7 eq24
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq39 eq26


@[equational_result]
theorem Equation22071_implies_Equation2 (G : Type*) [Magma G] (h : Equation22071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ (X2 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq51 (X0 X1 : G) : X0 = X1 := superpose eq7 eq31
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq154 eq51


@[equational_result]
theorem Equation22072_implies_Equation2 (G : Type*) [Magma G] (h : Equation22072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X5 := superpose eq7 eq7
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation22074_implies_Equation2 (G : Type*) [Magma G] (h : Equation22074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22075_implies_Equation2 (G : Type*) [Magma G] (h : Equation22075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22076_implies_Equation2 (G : Type*) [Magma G] (h : Equation22076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22077_implies_Equation2 (G : Type*) [Magma G] (h : Equation22077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22079_implies_Equation2 (G : Type*) [Magma G] (h : Equation22079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22080_implies_Equation2 (G : Type*) [Magma G] (h : Equation22080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22081_implies_Equation2 (G : Type*) [Magma G] (h : Equation22081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22082_implies_Equation2 (G : Type*) [Magma G] (h : Equation22082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22084_implies_Equation2 (G : Type*) [Magma G] (h : Equation22084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22085_implies_Equation2 (G : Type*) [Magma G] (h : Equation22085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22086_implies_Equation2 (G : Type*) [Magma G] (h : Equation22086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22087_implies_Equation2 (G : Type*) [Magma G] (h : Equation22087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22089_implies_Equation2 (G : Type*) [Magma G] (h : Equation22089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22090_implies_Equation2 (G : Type*) [Magma G] (h : Equation22090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22091_implies_Equation2 (G : Type*) [Magma G] (h : Equation22091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22092_implies_Equation2 (G : Type*) [Magma G] (h : Equation22092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22093_implies_Equation2 (G : Type*) [Magma G] (h : Equation22093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22095_implies_Equation2 (G : Type*) [Magma G] (h : Equation22095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq30 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ ((X2 ◇ X3) ◇ X0)) := superpose eq9 eq10
  have eq31 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq42 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq31 eq18
  have eq54 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq42 eq30
  have eq56 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq42 eq54
  have eq66 (X0 X1 : G) : X0 = X1 := superpose eq42 eq56
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq68 eq66


@[equational_result]
theorem Equation22096_implies_Equation2 (G : Type*) [Magma G] (h : Equation22096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ (X5 ◇ (X2 ◇ (X3 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ X0))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq32 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq10 eq9
  have eq42 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq32 eq12
  have eq44 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X0 := superpose eq42 eq7
  have eq55 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq42 eq44
  have eq58 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X0)) = X3 := superpose eq55 eq32
  have eq61 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq55 eq58
  have eq62 (X0 X3 : G) : X0 = X3 := superpose eq61 eq61
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq67 eq62


@[equational_result]
theorem Equation22097_implies_Equation2 (G : Type*) [Magma G] (h : Equation22097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ (X5 ◇ (X0 ◇ (X0 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq10 eq10
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq7 eq10
  have eq24 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ X0)) = X5 := superpose eq14 eq9
  have eq25 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq24 eq17
  have eq26 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq25 eq14
  have eq33 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq26 eq16
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq26 eq33
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq54 eq44


@[equational_result]
theorem Equation22098_implies_Equation2 (G : Type*) [Magma G] (h : Equation22098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ X2)) = ((X3 ◇ (X4 ◇ X5)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq14 eq12
  have eq22 (X0 X5 : G) : (X0 ◇ X5) = X5 := superpose eq14 eq10
  have eq27 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq22 eq21
  have eq29 (X0 X1 : G) : X0 = X1 := superpose eq22 eq27
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation22100_implies_Equation2 (G : Type*) [Magma G] (h : Equation22100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ (X1 ◇ X1))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ X2) := superpose eq9 eq9
  have eq31 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X2 := superpose eq7 eq11
  have eq46 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq31 eq18
  have eq54 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X1) = X5 := superpose eq31 eq9
  have eq65 (X1 X5 : G) : (X1 ◇ X1) = X5 := superpose eq46 eq54
  have eq91 (X0 X2 : G) : X0 = X2 := superpose eq65 eq65
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq91 eq8
  subsumption eq93 eq91


@[equational_result]
theorem Equation22101_implies_Equation2 (G : Type*) [Magma G] (h : Equation22101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq10
  have eq26 (X0 X1 X2 X6 X7 X8 X9 : G) : (X0 ◇ (X6 ◇ ((X1 ◇ X2) ◇ (X7 ◇ (X8 ◇ X9))))) = X6 := superpose eq9 eq9
  have eq36 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq10 eq9
  have eq49 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X6 := superpose eq36 eq26
  have eq55 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq49 eq15
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq55 eq55
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq75 eq67


@[equational_result]
theorem Equation22102_implies_Equation2 (G : Type*) [Magma G] (h : Equation22102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ (X3 ◇ X5))))) = X2 := superpose eq7 eq10
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq30
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq49
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq162 eq50


@[equational_result]
theorem Equation22103_implies_Equation2 (G : Type*) [Magma G] (h : Equation22103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X6))) = X5 := superpose eq7 eq7
  have eq26 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq10
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq29 eq26
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq48 eq48
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq62 eq50


@[equational_result]
theorem Equation22105_implies_Equation2 (G : Type*) [Magma G] (h : Equation22105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq31 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq18 eq15
  have eq41 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq63 eq41


@[equational_result]
theorem Equation22106_implies_Equation2 (G : Type*) [Magma G] (h : Equation22106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X0))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X2)) := superpose eq7 eq10
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq15 eq14
  have eq24 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq19 eq10
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq24 eq24
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation22107_implies_Equation2 (G : Type*) [Magma G] (h : Equation22107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ (X2 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq10 eq10
  have eq24 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq36 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq24 eq13
  have eq42 (X0 X2 : G) : X0 = X2 := superpose eq10 eq36
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq62 eq42


@[equational_result]
theorem Equation22108_implies_Equation2 (G : Type*) [Magma G] (h : Equation22108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ (X0 ◇ X6))) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq23 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq14 eq10
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation22110_implies_Equation2 (G : Type*) [Magma G] (h : Equation22110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X3 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq36 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq10
  have eq54 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X4 := superpose eq36 eq10
  have eq72 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq54 eq36
  have eq74 (X0 X3 : G) : X0 = X3 := superpose eq72 eq72
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq82 eq74


@[equational_result]
theorem Equation22111_implies_Equation2 (G : Type*) [Magma G] (h : Equation22111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ ((X0 ◇ (X4 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X3 ◇ X2) ◇ X0))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ X2)) = X5 := superpose eq7 eq9
  have eq14 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq13
  have eq24 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X2)) = X4 := superpose eq14 eq10
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq13 eq24
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq38 eq29


@[equational_result]
theorem Equation22112_implies_Equation2 (G : Type*) [Magma G] (h : Equation22112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ ((X0 ◇ (X4 ◇ X4)) ◇ (X0 ◇ (X4 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq9
  have eq14 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq13 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X3) = X0 := superpose eq14 eq7
  have eq16 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq14 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22113_implies_Equation2 (G : Type*) [Magma G] (h : Equation22113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ ((X3 ◇ X4) ◇ X6))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ (X6 ◇ X0)) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X7))) = X2 := superpose eq7 eq10
  have eq23 (X0 X2 X6 : G) : (X2 ◇ (X6 ◇ X0)) = X6 := superpose eq13 eq11
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq23 eq13
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq23 eq24
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq37 eq30


@[equational_result]
theorem Equation22115_implies_Equation2 (G : Type*) [Magma G] (h : Equation22115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X6 X7 : G) : ((X1 ◇ X0) ◇ (X6 ◇ (X7 ◇ X1))) = X6 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X1 ◇ (X2 ◇ X3))))) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X2)))) = X4 := superpose eq9 eq9
  have eq23 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq14 eq10
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22116_implies_Equation2 (G : Type*) [Magma G] (h : Equation22116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X0))) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X4)) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq21 (X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X4)) = X2 := superpose eq16 eq15
  have eq26 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq21 eq10
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation22117_implies_Equation2 (G : Type*) [Magma G] (h : Equation22117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 X6 X7 : G) : ((X1 ◇ X0) ◇ (X6 ◇ (X7 ◇ (X0 ◇ (X5 ◇ X4))))) = X6 := superpose eq7 eq7
  have eq10 (X0 X3 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X4 ◇ X3)))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X6 X7 : G) : ((X1 ◇ X0) ◇ X7) = X6 := superpose eq10 eq9
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation22118_implies_Equation2 (G : Type*) [Magma G] (h : Equation22118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X6))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq21 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq13 eq10
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation22119_implies_Equation2 (G : Type*) [Magma G] (h : Equation22119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X6 X7 X8 : G) : (X0 ◇ (X6 ◇ (X7 ◇ X8))) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq23 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq13 eq10
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation22121_implies_Equation2 (G : Type*) [Magma G] (h : Equation22121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq7 eq10
  have eq43 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq32 eq10
  have eq57 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = X4 := superpose eq32 eq43
  have eq58 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X3)) = X4 := superpose eq32 eq57
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq58 eq58
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq63 eq61


@[equational_result]
theorem Equation22122_implies_Equation2 (G : Type*) [Magma G] (h : Equation22122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X2) ◇ X4)) ◇ X0) = X1 := superpose eq7 eq7
  have eq41 (X0 X1 : G) : X0 = X1 := superpose eq10 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq51 eq41


@[equational_result]
theorem Equation22123_implies_Equation2 (G : Type*) [Magma G] (h : Equation22123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq7 eq39
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq119 eq63


@[equational_result]
theorem Equation22124_implies_Equation2 (G : Type*) [Magma G] (h : Equation22124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 X6 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq7
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq42 (X0 X5 : G) : X0 = X5 := superpose eq7 eq32
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq119 eq42


@[equational_result]
theorem Equation22126_implies_Equation2 (G : Type*) [Magma G] (h : Equation22126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22127_implies_Equation2 (G : Type*) [Magma G] (h : Equation22127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22128_implies_Equation2 (G : Type*) [Magma G] (h : Equation22128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22129_implies_Equation2 (G : Type*) [Magma G] (h : Equation22129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22131_implies_Equation2 (G : Type*) [Magma G] (h : Equation22131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22132_implies_Equation2 (G : Type*) [Magma G] (h : Equation22132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22133_implies_Equation2 (G : Type*) [Magma G] (h : Equation22133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation22134_implies_Equation2 (G : Type*) [Magma G] (h : Equation22134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22136_implies_Equation2 (G : Type*) [Magma G] (h : Equation22136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22137_implies_Equation2 (G : Type*) [Magma G] (h : Equation22137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22138_implies_Equation2 (G : Type*) [Magma G] (h : Equation22138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22139_implies_Equation2 (G : Type*) [Magma G] (h : Equation22139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22141_implies_Equation2 (G : Type*) [Magma G] (h : Equation22141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22142_implies_Equation2 (G : Type*) [Magma G] (h : Equation22142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22143_implies_Equation2 (G : Type*) [Magma G] (h : Equation22143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22144_implies_Equation2 (G : Type*) [Magma G] (h : Equation22144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22145_implies_Equation2 (G : Type*) [Magma G] (h : Equation22145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22147_implies_Equation2 (G : Type*) [Magma G] (h : Equation22147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X3 := superpose eq10 eq10
  have eq24 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq14 eq10
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation22148_implies_Equation2 (G : Type*) [Magma G] (h : Equation22148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ (X4 ◇ X2))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq145 eq39


@[equational_result]
theorem Equation22149_implies_Equation2 (G : Type*) [Magma G] (h : Equation22149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ (X4 ◇ (X0 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq10 eq10
  have eq25 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq14 eq10
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq7 eq25
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation22150_implies_Equation2 (G : Type*) [Magma G] (h : Equation22150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) ◇ X0) = X3 := superpose eq7 eq7
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq43 eq33


@[equational_result]
theorem Equation22152_implies_Equation2 (G : Type*) [Magma G] (h : Equation22152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22153_implies_Equation2 (G : Type*) [Magma G] (h : Equation22153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22154_implies_Equation2 (G : Type*) [Magma G] (h : Equation22154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22155_implies_Equation2 (G : Type*) [Magma G] (h : Equation22155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22157_implies_Equation2 (G : Type*) [Magma G] (h : Equation22157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22158_implies_Equation2 (G : Type*) [Magma G] (h : Equation22158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22159_implies_Equation2 (G : Type*) [Magma G] (h : Equation22159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22160_implies_Equation2 (G : Type*) [Magma G] (h : Equation22160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22162_implies_Equation2 (G : Type*) [Magma G] (h : Equation22162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22163_implies_Equation2 (G : Type*) [Magma G] (h : Equation22163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22164_implies_Equation2 (G : Type*) [Magma G] (h : Equation22164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22165_implies_Equation2 (G : Type*) [Magma G] (h : Equation22165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22167_implies_Equation2 (G : Type*) [Magma G] (h : Equation22167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22168_implies_Equation2 (G : Type*) [Magma G] (h : Equation22168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22169_implies_Equation2 (G : Type*) [Magma G] (h : Equation22169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22170_implies_Equation2 (G : Type*) [Magma G] (h : Equation22170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22171_implies_Equation2 (G : Type*) [Magma G] (h : Equation22171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22173_implies_Equation2 (G : Type*) [Magma G] (h : Equation22173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X3 := superpose eq10 eq10
  have eq39 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq10
  have eq51 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq39 eq35
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq51
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq106 eq68


@[equational_result]
theorem Equation22174_implies_Equation2 (G : Type*) [Magma G] (h : Equation22174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X4 ◇ (X0 ◇ X3)) ◇ (X5 ◇ (X2 ◇ (X3 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X0 ◇ X2) ◇ (X4 ◇ X3))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq10
  have eq23 (X0 X1 X2 X5 : G) : ((X1 ◇ X0) ◇ X2) = X5 := superpose eq13 eq9
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq51 eq29


@[equational_result]
theorem Equation22175_implies_Equation2 (G : Type*) [Magma G] (h : Equation22175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X5 ◇ (X4 ◇ (X0 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X0 ◇ X3) ◇ (X4 ◇ (X0 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X0))) = X3 := superpose eq10 eq10
  have eq20 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ X0)) = X5 := superpose eq13 eq9
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq20 eq20
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq52 eq33


@[equational_result]
theorem Equation22176_implies_Equation2 (G : Type*) [Magma G] (h : Equation22176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X0 ◇ X4) ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq10 eq10
  have eq23 (X0 X3 X5 : G) : (X3 ◇ X0) = X5 := superpose eq14 eq12
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22178_implies_Equation2 (G : Type*) [Magma G] (h : Equation22178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22179_implies_Equation2 (G : Type*) [Magma G] (h : Equation22179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22180_implies_Equation2 (G : Type*) [Magma G] (h : Equation22180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22181_implies_Equation2 (G : Type*) [Magma G] (h : Equation22181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22183_implies_Equation2 (G : Type*) [Magma G] (h : Equation22183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22184_implies_Equation2 (G : Type*) [Magma G] (h : Equation22184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22185_implies_Equation2 (G : Type*) [Magma G] (h : Equation22185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22186_implies_Equation2 (G : Type*) [Magma G] (h : Equation22186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22188_implies_Equation2 (G : Type*) [Magma G] (h : Equation22188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22189_implies_Equation2 (G : Type*) [Magma G] (h : Equation22189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22190_implies_Equation2 (G : Type*) [Magma G] (h : Equation22190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22191_implies_Equation2 (G : Type*) [Magma G] (h : Equation22191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22193_implies_Equation2 (G : Type*) [Magma G] (h : Equation22193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22194_implies_Equation2 (G : Type*) [Magma G] (h : Equation22194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22195_implies_Equation2 (G : Type*) [Magma G] (h : Equation22195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22196_implies_Equation2 (G : Type*) [Magma G] (h : Equation22196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22197_implies_Equation2 (G : Type*) [Magma G] (h : Equation22197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22199_implies_Equation2 (G : Type*) [Magma G] (h : Equation22199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X6 X7 : G) : ((X1 ◇ X0) ◇ (X6 ◇ (X7 ◇ X1))) = X7 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X1 ◇ (X2 ◇ X3))))) = X6 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X2)))) = X5 := superpose eq9 eq9
  have eq23 (X0 X1 X6 : G) : (X0 ◇ X1) = X6 := superpose eq14 eq10
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22200_implies_Equation2 (G : Type*) [Magma G] (h : Equation22200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X6 X7 : G) : ((X1 ◇ X0) ◇ (X6 ◇ (X7 ◇ (X2 ◇ (X3 ◇ X4))))) = X7 := superpose eq7 eq7
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X4))) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X7 : G) : ((X1 ◇ X0) ◇ X2) = X7 := superpose eq10 eq9
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq46 eq17


@[equational_result]
theorem Equation22201_implies_Equation2 (G : Type*) [Magma G] (h : Equation22201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X0 ◇ X3)))) = X6 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X6 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X6 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq10 eq10
  have eq25 (X0 X6 : G) : (X0 ◇ X0) = X6 := superpose eq14 eq12
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq7 eq25
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation22202_implies_Equation2 (G : Type*) [Magma G] (h : Equation22202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X5))) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation22203_implies_Equation2 (G : Type*) [Magma G] (h : Equation22203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X7 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X7 := superpose eq7 eq7
  have eq29 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation22205_implies_Equation2 (G : Type*) [Magma G] (h : Equation22205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22206_implies_Equation2 (G : Type*) [Magma G] (h : Equation22206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22207_implies_Equation2 (G : Type*) [Magma G] (h : Equation22207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22208_implies_Equation2 (G : Type*) [Magma G] (h : Equation22208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22209_implies_Equation2 (G : Type*) [Magma G] (h : Equation22209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X1 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22211_implies_Equation2 (G : Type*) [Magma G] (h : Equation22211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22212_implies_Equation2 (G : Type*) [Magma G] (h : Equation22212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22213_implies_Equation2 (G : Type*) [Magma G] (h : Equation22213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22214_implies_Equation2 (G : Type*) [Magma G] (h : Equation22214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22215_implies_Equation2 (G : Type*) [Magma G] (h : Equation22215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X2 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22217_implies_Equation2 (G : Type*) [Magma G] (h : Equation22217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22218_implies_Equation2 (G : Type*) [Magma G] (h : Equation22218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22219_implies_Equation2 (G : Type*) [Magma G] (h : Equation22219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22220_implies_Equation2 (G : Type*) [Magma G] (h : Equation22220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22221_implies_Equation2 (G : Type*) [Magma G] (h : Equation22221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X3 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22223_implies_Equation2 (G : Type*) [Magma G] (h : Equation22223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22224_implies_Equation2 (G : Type*) [Magma G] (h : Equation22224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22225_implies_Equation2 (G : Type*) [Magma G] (h : Equation22225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22226_implies_Equation2 (G : Type*) [Magma G] (h : Equation22226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22227_implies_Equation2 (G : Type*) [Magma G] (h : Equation22227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22229_implies_Equation2 (G : Type*) [Magma G] (h : Equation22229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22230_implies_Equation2 (G : Type*) [Magma G] (h : Equation22230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22231_implies_Equation2 (G : Type*) [Magma G] (h : Equation22231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22232_implies_Equation2 (G : Type*) [Magma G] (h : Equation22232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22233_implies_Equation2 (G : Type*) [Magma G] (h : Equation22233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22234_implies_Equation2 (G : Type*) [Magma G] (h : Equation22234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X5 ◇ X6))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22440_implies_Equation2 (G : Type*) [Magma G] (h : Equation22440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X4)) = (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) := superpose eq10 eq10
  have eq21 (X0 X1 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq10 eq10
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq10 eq9
  have eq41 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq18
  have eq42 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X3)) = X1 := superpose eq41 eq23
  have eq48 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((X3 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) := superpose eq10 eq11
  have eq133 (X0 X1 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) ◇ X4)) := superpose eq7 eq31
  have eq369 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq31 eq48
  have eq405 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X3)) = (((X1 ◇ X1) ◇ X3) ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq10 eq369
  have eq406 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq369 eq369
  have eq461 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq369 eq10
  have eq482 (X1 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ ((X1 ◇ X1) ◇ X3)) = X1 := superpose eq42 eq405
  have eq486 (X0 X1 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) ◇ X4)) = X0 := superpose eq482 eq133
  have eq487 (X0 X1 X3 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X3)) := superpose eq482 eq21
  have eq488 (X0 X1 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X4)) = X0 := superpose eq487 eq486
  have eq505 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := superpose eq41 eq461
  have eq514 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq505 eq406
  have eq598 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) ◇ X4)) := superpose eq487 eq42
  have eq614 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq514 eq598
  have eq615 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq488 eq614
  have eq898 (X0 X1 : G) : X0 = X1 := superpose eq7 eq615
  have eq948 (X0 : G) : sK0 ≠ X0 := superpose eq898 eq8
  subsumption eq948 eq898


@[equational_result]
theorem Equation22443_implies_Equation2 (G : Type*) [Magma G] (h : Equation22443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq11
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) ◇ X2)) = X1 := superpose eq11 eq7
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq22 eq9
  have eq133 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) := superpose eq12 eq9
  have eq145 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq11 eq133
  have eq146 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq145 eq33
  have eq149 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq146 eq14
  have eq206 (X0 X1 : G) : X0 = X1 := superpose eq11 eq149
  have eq292 (X0 : G) : sK0 ≠ X0 := superpose eq206 eq8
  subsumption eq292 eq206


@[equational_result]
theorem Equation22445_implies_Equation2 (G : Type*) [Magma G] (h : Equation22445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (((X0 ◇ X3) ◇ (X3 ◇ X3)) ◇ (X1 ◇ (X0 ◇ X0))) = X3 := superpose eq7 eq12
  have eq47 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq12 eq13
  have eq64 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq47 eq9
  have eq77 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2)))) = (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq13 eq64
  have eq78 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq64 eq64
  have eq113 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq47 eq78
  have eq114 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq113 eq77
  have eq125 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X3) = X1 := superpose eq12 eq47
  have eq171 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq125 eq114
  have eq273 (X0 X3 : G) : X0 = X3 := superpose eq7 eq171
  have eq500 (X0 : G) : sK0 ≠ X0 := superpose eq273 eq8
  subsumption eq500 eq273


@[equational_result]
theorem Equation22447_implies_Equation2 (G : Type*) [Magma G] (h : Equation22447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq125 eq38


@[equational_result]
theorem Equation22450_implies_Equation2 (G : Type*) [Magma G] (h : Equation22450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq9 eq7
  have eq39 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X2 := superpose eq9 eq25
  have eq106 (X0 X2 : G) : X0 = X2 := superpose eq7 eq39
  have eq220 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq220 eq106


@[equational_result]
theorem Equation22453_implies_Equation2 (G : Type*) [Magma G] (h : Equation22453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) ◇ X2)) = X1 := superpose eq10 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) ◇ X2)) = X1 := superpose eq12 eq14
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq7 eq9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq7
  have eq30 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq25 eq16
  have eq31 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq30 eq17
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X2)) := superpose eq31 eq9
  have eq39 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq33
  have eq80 (X0 X2 : G) : X0 = X2 := superpose eq39 eq39
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq82 eq80


@[equational_result]
theorem Equation22457_implies_Equation2 (G : Type*) [Magma G] (h : Equation22457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X5)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X5 : G) : (X0 ◇ (X0 ◇ X5)) = X2 := superpose eq11 eq10
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq43 eq17


@[equational_result]
theorem Equation22459_implies_Equation2 (G : Type*) [Magma G] (h : Equation22459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ ((X2 ◇ X0) ◇ X3))) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X2)))) := superpose eq7 eq10
  have eq51 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) = ((X3 ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))))) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq13 eq7
  have eq59 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))))) = (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)))))) ◇ X2)) := superpose eq13 eq9
  have eq63 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq7 eq9
  have eq89 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq63 eq63
  have eq140 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) ◇ X1)))) ◇ X2)) := superpose eq89 eq59
  have eq177 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) = ((((X4 ◇ X0) ◇ X2) ◇ (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3))) ◇ X0) := superpose eq7 eq11
  have eq178 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = ((((X4 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq11
  have eq185 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) := superpose eq11 eq12
  have eq203 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq185
  have eq205 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X1) := superpose eq11 eq185
  have eq240 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) := superpose eq205 eq177
  have eq241 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1)))) ◇ X2)) := superpose eq205 eq140
  have eq243 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (((X0 ◇ X0) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq240 eq178
  have eq253 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) = ((X3 ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) := superpose eq240 eq51
  have eq269 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq203 eq243
  have eq305 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) = X2 := superpose eq7 eq253
  have eq311 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1))) := superpose eq269 eq241
  have eq312 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq240 eq311
  have eq313 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) = X1 := superpose eq269 eq312
  have eq314 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq313 eq305
  have eq351 (X0 X1 : G) : X0 = X1 := superpose eq7 eq314
  have eq444 (X0 : G) : sK0 ≠ X0 := superpose eq351 eq8
  subsumption eq444 eq351


@[equational_result]
theorem Equation22460_implies_Equation2 (G : Type*) [Magma G] (h : Equation22460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose eq11 eq7
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq7 eq9
  have eq59 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1) = ((X3 ◇ (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1))) ◇ X0) := superpose eq7 eq10
  have eq77 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = ((X3 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))) := superpose eq22 eq22
  have eq82 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq16 eq22
  have eq85 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) = X1 := superpose eq22 eq7
  have eq89 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ ((X3 ◇ X1) ◇ X3)) = X1 := superpose eq22 eq7
  have eq130 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2)))))) = ((X4 ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2)))))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2)))))))) ◇ X2) := superpose eq22 eq59
  have eq135 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) = (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1)) ◇ (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) ◇ (X4 ◇ (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1))))) ◇ X3) := superpose eq22 eq59
  have eq141 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) ◇ X0) ◇ ((X4 ◇ X2) ◇ X4)) = X2 := superpose eq59 eq7
  have eq143 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) ◇ X0) ◇ X2) := superpose eq59 eq11
  have eq148 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X2 ◇ X2)) = (((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0) ◇ ((X4 ◇ (((X2 ◇ X2) ◇ X2) ◇ (X2 ◇ X2))) ◇ X4)) := superpose eq59 eq9
  have eq156 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ ((X3 ◇ X1) ◇ (X1 ◇ (X4 ◇ (X1 ◇ X1))))) = X1 := superpose eq22 eq85
  have eq188 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2)))))) = ((X4 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) := superpose eq156 eq130
  have eq276 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X3 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) := superpose eq7 eq89
  have eq294 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ (((X2 ◇ X0) ◇ X2) ◇ ((X2 ◇ X0) ◇ X2))))) ◇ (X0 ◇ ((X4 ◇ X0) ◇ (X0 ◇ (X5 ◇ (X0 ◇ X0)))))) := superpose eq89 eq89
  have eq305 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = (((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0))))))) ◇ X0) := superpose eq89 eq89
  have eq309 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq89 eq59
  have eq351 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq309 eq82
  have eq416 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq351
  have eq444 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq309 eq416
  have eq448 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := superpose eq444 eq22
  have eq460 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0) ◇ ((X4 ◇ X2) ◇ X4)) = X2 := superpose eq444 eq148
  have eq501 (X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X2)) = ((X4 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) := superpose eq448 eq188
  have eq502 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = ((X0 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq448 eq305
  have eq505 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) = (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) ◇ X3) := superpose eq448 eq135
  have eq506 (X0 X2 X4 X5 : G) : ((X2 ◇ X0) ◇ X2) = (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X4 ◇ X0) ◇ (X0 ◇ (X5 ◇ (X0 ◇ X0)))))) := superpose eq448 eq294
  have eq509 (X1 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq448 eq77
  have eq528 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) := superpose eq501 eq276
  have eq530 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X0 ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq501 eq502
  have eq546 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := superpose eq530 eq448
  have eq560 (X0 X2 X4 X5 : G) : ((X2 ◇ X0) ◇ X2) = (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X4 ◇ X0) ◇ (X5 ◇ (X0 ◇ X0))))) := superpose eq530 eq506
  have eq561 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq546 eq560
  have eq564 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq509 eq11
  have eq567 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X4 ◇ X2) ◇ X4)) = X2 := superpose eq509 eq141
  have eq569 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0) ◇ X2) := superpose eq509 eq143
  have eq581 (X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) := superpose eq569 eq505
  have eq583 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq581 eq528
  have eq589 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X0 := superpose eq309 eq583
  have eq591 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq589 eq561
  have eq613 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ ((X4 ◇ X2) ◇ X4)) = X2 := superpose eq591 eq567
  have eq615 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X2 := superpose eq591 eq613
  have eq616 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq615 eq564
  have eq618 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq616 eq589
  have eq719 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0) ◇ X4) = X2 := superpose eq618 eq460
  have eq720 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq618 eq719
  have eq721 (X0 X1 : G) : X0 = X1 := superpose eq616 eq720
  have eq740 (X0 : G) : sK0 ≠ X0 := superpose eq721 eq8
  subsumption eq740 eq721


@[equational_result]
theorem Equation22461_implies_Equation2 (G : Type*) [Magma G] (h : Equation22461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X0) = (X0 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ ((X2 ◇ X0) ◇ X3))) ◇ (X0 ◇ X5)) := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 X5 : G) : (((X2 ◇ X0) ◇ X3) ◇ ((X4 ◇ X0) ◇ X5)) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ X0) ◇ (X0 ◇ X5)) := superpose eq13 eq11
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X2) = X0 := superpose eq7 eq21
  have eq68 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq39 eq39
  have eq118 (X0 X4 : G) : X0 = X4 := superpose eq7 eq68
  have eq194 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq194 eq118


@[equational_result]
theorem Equation22463_implies_Equation2 (G : Type*) [Magma G] (h : Equation22463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq9
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X4 ◇ X4)) ◇ X5) = X4 := superpose eq9 eq14
  have eq23 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ X4) = X3 := superpose eq14 eq14
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ X2) := superpose eq9 eq14
  have eq38 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq23 eq25
  have eq39 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X5) = X4 := superpose eq38 eq20
  have eq52 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq38 eq39
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq52 eq52
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq58 eq53


@[equational_result]
theorem Equation22465_implies_Equation2 (G : Type*) [Magma G] (h : Equation22465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X1) = (X0 ◇ ((X3 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) ◇ X3)) = X1 := superpose eq11 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) = X2 := superpose eq11 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) ◇ X3)) = X1 := superpose eq13 eq15
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X1) ◇ X3)) = X1 := superpose eq16 eq18
  have eq40 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) ◇ (X4 ◇ X4)) ◇ X2) = X4 := superpose eq9 eq11
  have eq54 (X0 X2 X4 : G) : (((X2 ◇ (X0 ◇ X0)) ◇ (X4 ◇ X4)) ◇ X2) = X4 := superpose eq19 eq40
  have eq55 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq16 eq54
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq55
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq142 eq56


@[equational_result]
theorem Equation22467_implies_Equation2 (G : Type*) [Magma G] (h : Equation22467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq11 eq11
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq18 eq12
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22468_implies_Equation2 (G : Type*) [Magma G] (h : Equation22468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) ◇ ((X3 ◇ X3) ◇ X3)) := superpose eq9 eq9
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X3) ◇ (X3 ◇ X3)) ◇ (X3 ◇ X3)) = ((X4 ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2))) := superpose eq9 eq9
  have eq18 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) ◇ ((X3 ◇ X3) ◇ X3)) = X1 := superpose eq18 eq14
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq10
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := superpose eq27 eq9
  have eq34 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2))) = X3 := superpose eq27 eq17
  have eq39 (X1 X3 : G) : (X1 ◇ ((X3 ◇ X3) ◇ X3)) = X1 := superpose eq30 eq22
  have eq43 (X1 X3 X4 : G) : ((X4 ◇ X3) ◇ X1) = X3 := superpose eq30 eq34
  have eq46 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq43 eq39
  have eq48 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq46 eq27
  have eq51 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq46 eq48
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq51 eq51
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq57 eq52


@[equational_result]
theorem Equation22469_implies_Equation2 (G : Type*) [Magma G] (h : Equation22469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation22471_implies_Equation2 (G : Type*) [Magma G] (h : Equation22471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq34 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq12 eq12
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq34
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq140 eq42


@[equational_result]
theorem Equation22472_implies_Equation2 (G : Type*) [Magma G] (h : Equation22472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq128 eq34


@[equational_result]
theorem Equation22473_implies_Equation2 (G : Type*) [Magma G] (h : Equation22473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ ((X3 ◇ X4) ◇ X4)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ ((X4 ◇ X5) ◇ X5))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq10
  have eq22 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := superpose eq16 eq9
  have eq31 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq22
  have eq42 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq31 eq16
  have eq63 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq31 eq42
  have eq67 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq63 eq42
  have eq70 (X0 X1 : G) : X0 = X1 := superpose eq31 eq67
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq89 eq70


@[equational_result]
theorem Equation22474_implies_Equation2 (G : Type*) [Magma G] (h : Equation22474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation22477_implies_Equation2 (G : Type*) [Magma G] (h : Equation22477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq10 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X1)) = (X0 ◇ (((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X1)) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X1))) ◇ X3)) := superpose eq7 eq9
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) := superpose eq7 eq9
  have eq70 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = ((((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X3)) := superpose eq26 eq26
  have eq82 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq15 eq26
  have eq86 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq26 eq7
  have eq139 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = ((X3 ◇ (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X3)) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0))) := superpose eq19 eq11
  have eq178 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X1)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3))) := superpose eq7 eq86
  have eq199 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) = (X3 ◇ (((((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) ◇ X4)) := superpose eq86 eq19
  have eq200 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq86 eq19
  have eq227 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq200 eq82
  have eq300 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq7 eq227
  have eq323 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq200 eq300
  have eq325 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq323 eq26
  have eq338 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0))) = X1 := superpose eq323 eq139
  have eq367 (X0 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq325 eq70
  have eq377 (X0 X3 X4 : G) : (X0 ◇ X0) = (X3 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X4)) := superpose eq325 eq199
  have eq397 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq367 eq227
  have eq415 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) := superpose eq397 eq178
  have eq455 (X0 X3 X4 : G) : (X0 ◇ X0) = (X3 ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq397 eq377
  have eq456 (X0 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = X0 := superpose eq397 eq455
  have eq457 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq456 eq415
  have eq542 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X3)) ◇ X0) = X1 := superpose eq457 eq338
  have eq543 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq457 eq542
  have eq544 (X0 X1 : G) : X0 = X1 := superpose eq397 eq543
  have eq552 (X0 : G) : sK0 ≠ X0 := superpose eq544 eq8
  subsumption eq552 eq544


@[equational_result]
theorem Equation22480_implies_Equation2 (G : Type*) [Magma G] (h : Equation22480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X2)) := superpose eq7 eq9
  have eq64 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = X0 := superpose eq22 eq7
  have eq72 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X3) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X4)) := superpose eq7 eq10
  have eq124 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq64 eq72
  have eq230 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq124 eq124
  have eq254 (X0 X2 : G) : X0 = X2 := superpose eq7 eq230
  have eq329 (X0 : G) : sK0 ≠ X0 := superpose eq254 eq8
  subsumption eq329 eq254


@[equational_result]
theorem Equation22482_implies_Equation2 (G : Type*) [Magma G] (h : Equation22482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (((X0 ◇ X3) ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X1 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq11
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X0 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) ◇ X1) := superpose eq7 eq11
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((X1 ◇ X0) ◇ (((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X3) ◇ X1)) := superpose eq11 eq7
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq11 eq10
  have eq34 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) ◇ X1)) := superpose eq24 eq18
  have eq35 (X0 X2 : G) : (((X0 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq24 eq11
  have eq43 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose eq35 eq7
  have eq78 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq43 eq43
  have eq80 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq43 eq10
  have eq93 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq78
  have eq94 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq7 eq80
  have eq132 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq12 eq93
  have eq137 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := superpose eq93 eq7
  have eq142 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq93 eq10
  have eq145 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq93 eq12
  have eq153 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq137 eq145
  have eq154 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq153 eq132
  have eq155 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq93 eq154
  have eq173 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X0 := superpose eq35 eq14
  have eq180 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq14 eq10
  have eq200 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) := superpose eq7 eq180
  have eq217 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq7 eq94
  have eq219 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq35 eq94
  have eq237 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq94 eq12
  have eq250 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) = ((X0 ◇ X1) ◇ X0) := superpose eq200 eq237
  have eq262 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq250 eq173
  have eq272 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq262 eq155
  have eq277 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq272 eq93
  have eq278 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) := superpose eq272 eq142
  have eq279 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq272 eq153
  have eq293 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq277 eq279
  have eq294 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq293 eq217
  have eq295 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq294 eq278
  have eq296 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq293 eq295
  have eq297 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq277 eq296
  have eq302 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq297 eq219
  have eq350 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := superpose eq302 eq34
  have eq351 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq302 eq35
  have eq360 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq351 eq350
  have eq378 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq351 eq360
  have eq379 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq351 eq378
  have eq428 (X0 X1 : G) : X0 = X1 := superpose eq351 eq379
  have eq430 (X0 : G) : sK0 ≠ X0 := superpose eq428 eq8
  subsumption eq430 eq428


@[equational_result]
theorem Equation22484_implies_Equation2 (G : Type*) [Magma G] (h : Equation22484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq128 eq40


@[equational_result]
theorem Equation22487_implies_Equation2 (G : Type*) [Magma G] (h : Equation22487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((X1 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq10 eq7
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq10 eq31
  have eq60 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X3)) := superpose eq46 eq11
  have eq86 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = (((X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq60 eq60
  have eq93 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) = (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) := superpose eq7 eq60
  have eq100 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X1) ◇ (X1 ◇ X2)) := superpose eq60 eq60
  have eq112 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X2)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X3))) = X3 := superpose eq60 eq31
  have eq120 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)) ◇ X3)) := superpose eq60 eq10
  have eq142 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) = (X0 ◇ X0) := superpose eq46 eq93
  have eq143 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ X0) := superpose eq46 eq142
  have eq154 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq143 eq10
  have eq173 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = (((X3 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq143 eq86
  have eq183 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq143 eq12
  have eq211 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) := superpose eq183 eq154
  have eq230 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = (((X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq183 eq173
  have eq273 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (X1 ◇ X2)) := superpose eq143 eq100
  have eq274 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X2)) := superpose eq183 eq273
  have eq275 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X1 ◇ X1) ◇ (X1 ◇ X2)) := superpose eq143 eq274
  have eq305 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X3))) = X3 := superpose eq143 eq112
  have eq306 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X3))) = X3 := superpose eq183 eq305
  have eq331 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq143 eq120
  have eq332 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X1) := superpose eq143 eq331
  have eq333 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq183 eq332
  have eq334 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq333 eq211
  have eq352 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ (X2 ◇ X1)) := superpose eq183 eq334
  have eq353 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = ((X1 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)))) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq352 eq230
  have eq366 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X3))) = X3 := superpose eq352 eq306
  have eq380 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq143 eq353
  have eq381 (X0 X1 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X5)) = ((X1 ◇ X3) ◇ X4) := superpose eq352 eq380
  have eq402 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X4)) = X3 := superpose eq352 eq366
  have eq403 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X4)) = X3 := superpose eq352 eq402
  have eq404 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X1 := superpose eq403 eq275
  have eq411 (X1 X3 X4 : G) : ((X1 ◇ X3) ◇ X4) = X1 := superpose eq404 eq381
  have eq426 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq411 eq333
  have eq427 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq426 eq143
  have eq434 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X1 := superpose eq427 eq352
  have eq439 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq427 eq434
  have eq440 (X0 X3 : G) : X0 = X3 := superpose eq439 eq439
  have eq442 (X0 : G) : sK0 ≠ X0 := superpose eq440 eq8
  subsumption eq442 eq440


@[equational_result]
theorem Equation22490_implies_Equation2 (G : Type*) [Magma G] (h : Equation22490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq40 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq15
  have eq102 (X0 X2 : G) : X0 = X2 := superpose eq40 eq40
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq182 eq102


@[equational_result]
theorem Equation22492_implies_Equation2 (G : Type*) [Magma G] (h : Equation22492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) = (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0) ◇ (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) := superpose eq10 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq9 eq9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1)) = X0 := superpose eq7 eq9
  have eq30 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq20 eq20
  have eq66 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq30 eq7
  have eq83 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1))) = (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq66 eq15
  have eq87 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (((X0 ◇ (((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X1)))) = (X0 ◇ (((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X4) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq20 eq14
  have eq110 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (((((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ (((((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X4) ◇ (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq14 eq7
  have eq125 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq20 eq66
  have eq151 (X0 X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X4) ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))) := superpose eq125 eq87
  have eq153 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq125 eq10
  have eq157 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (((((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X4) ◇ (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq125 eq110
  have eq162 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq125 eq83
  have eq190 (X0 X1 X2 X4 : G) : (X0 ◇ (((X2 ◇ X1) ◇ X4) ◇ (X2 ◇ X1))) = X1 := superpose eq125 eq151
  have eq193 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq125 eq153
  have eq196 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := superpose eq190 eq157
  have eq197 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq125 eq196
  have eq202 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq197 eq66
  have eq204 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = X1 := superpose eq197 eq190
  have eq214 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X1 := superpose eq197 eq204
  have eq223 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq214 eq162
  have eq224 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq202 eq223
  have eq226 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq224 eq193
  have eq233 (X0 X3 : G) : X0 = X3 := superpose eq226 eq226
  have eq235 (X0 : G) : sK0 ≠ X0 := superpose eq233 eq8
  subsumption eq235 eq233


@[equational_result]
theorem Equation22493_implies_Equation2 (G : Type*) [Magma G] (h : Equation22493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq12 eq7
  have eq44 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq16 eq16
  have eq51 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq16 eq7
  have eq61 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X3) ◇ X3)) := superpose eq16 eq9
  have eq64 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) = (((X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0)) ◇ X3) ◇ (((X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0)) ◇ X4) ◇ X4)) := superpose eq9 eq9
  have eq68 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = ((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ (X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0))) := superpose eq9 eq9
  have eq71 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1)) = X0 := superpose eq7 eq9
  have eq73 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0))) = X3 := superpose eq9 eq7
  have eq76 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = ((((X0 ◇ X2) ◇ X2) ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X3)) := superpose eq9 eq10
  have eq84 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq51 eq61
  have eq95 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2)) ◇ X1) := superpose eq10 eq44
  have eq99 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq16 eq44
  have eq104 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq44 eq10
  have eq114 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2)) ◇ X1) := superpose eq16 eq95
  have eq117 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose eq84 eq104
  have eq118 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq99 eq117
  have eq119 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2)) := superpose eq118 eq10
  have eq147 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq119 eq114
  have eq163 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) = (((X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0)) ◇ X3) ◇ (((X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0)) ◇ X4) ◇ X4)) := superpose eq147 eq64
  have eq165 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X1 ◇ X0) ◇ X3) ◇ (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0))) := superpose eq147 eq68
  have eq166 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := superpose eq147 eq71
  have eq167 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0))) = X3 := superpose eq147 eq73
  have eq169 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X3)) := superpose eq147 eq76
  have eq204 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) = (((X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0)) ◇ X3) ◇ (X4 ◇ (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0)))) := superpose eq147 eq163
  have eq205 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) = (((X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X3) ◇ (X4 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)))) := superpose eq147 eq204
  have eq208 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X1 ◇ X0) ◇ X3) ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq147 eq165
  have eq209 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (((X1 ◇ X0) ◇ X3) ◇ X2) := superpose eq166 eq208
  have eq210 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) = ((X2 ◇ X3) ◇ (X4 ◇ X2)) := superpose eq166 eq205
  have eq212 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0))) = X3 := superpose eq147 eq167
  have eq213 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) ◇ X2) = X3 := superpose eq166 eq212
  have eq214 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (((X2 ◇ X0) ◇ X1) ◇ X0)) := superpose eq209 eq169
  have eq215 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq209 eq214
  have eq216 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq209 eq215
  have eq217 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq118 eq216
  have eq223 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X2) = X3 := superpose eq217 eq213
  have eq250 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq223 eq166
  have eq251 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq250 eq147
  have eq255 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X0)) = ((X2 ◇ X3) ◇ (X4 ◇ X2)) := superpose eq250 eq210
  have eq262 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = ((X2 ◇ X3) ◇ X2) := superpose eq250 eq255
  have eq263 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X0)) = (X3 ◇ X2) := superpose eq250 eq262
  have eq264 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq251 eq263
  have eq265 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq250 eq264
  have eq270 (X0 X1 : G) : X0 = X1 := superpose eq250 eq265
  have eq284 (X0 : G) : sK0 ≠ X0 := superpose eq270 eq8
  subsumption eq284 eq270


@[equational_result]
theorem Equation22494_implies_Equation2 (G : Type*) [Magma G] (h : Equation22494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X5)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X5 : G) : (X0 ◇ (X0 ◇ X5)) = X2 := superpose eq12 eq11
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation22496_implies_Equation2 (G : Type*) [Magma G] (h : Equation22496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ ((X3 ◇ (X2 ◇ (X0 ◇ X2))) ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := superpose eq7 eq10
  have eq32 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq11 eq10
  have eq36 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ X3) = ((X4 ◇ (((X0 ◇ X1) ◇ X3) ◇ X4)) ◇ (X0 ◇ X4)) := superpose eq11 eq10
  have eq40 (X0 X2 : G) : (X0 ◇ X2) = (((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ X0) := superpose eq32 eq11
  have eq64 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) = (((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq40
  have eq67 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) = (((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq40 eq40
  have eq71 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq40 eq7
  have eq84 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) = (((X2 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0) := superpose eq7 eq71
  have eq86 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) = (((X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ (((X1 ◇ X3) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq10 eq71
  have eq88 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) = ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X1)) := superpose eq40 eq71
  have eq89 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = X1 := superpose eq71 eq14
  have eq92 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq71 eq10
  have eq134 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (((X3 ◇ X1) ◇ X0) ◇ X1)) = (((((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (((X3 ◇ X1) ◇ X0) ◇ X1))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0))) := superpose eq9 eq40
  have eq136 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (((X3 ◇ X1) ◇ X0) ◇ X1)) = (((((X3 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (((X3 ◇ X1) ◇ X0) ◇ X1)) ◇ (((X3 ◇ X1) ◇ X0) ◇ X1))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq9 eq71
  have eq156 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq89 eq14
  have eq160 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (((X1 ◇ X0) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))) := superpose eq89 eq7
  have eq161 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq89 eq7
  have eq163 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X0) = ((((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))) := superpose eq89 eq9
  have eq164 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X3) = (((X2 ◇ X0) ◇ (((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X3) ◇ (X2 ◇ X0))) ◇ X0) := superpose eq89 eq10
  have eq225 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) = X0 := superpose eq7 eq161
  have eq245 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X4))) = (((X1 ◇ X4) ◇ ((X3 ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X4))) ◇ (X1 ◇ X4))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq10 eq161
  have eq399 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = X1 := superpose eq89 eq225
  have eq447 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X3)) = X0 := superpose eq7 eq36
  have eq467 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq71 eq36
  have eq522 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq447 eq447
  have eq535 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X0) = X3 := superpose eq447 eq447
  have eq542 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X2 := superpose eq40 eq447
  have eq593 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq522 eq160
  have eq601 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = ((X2 ◇ (X0 ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq522 eq467
  have eq602 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = ((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq522 eq92
  have eq617 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X0) = ((((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X0)))) := superpose eq593 eq163
  have eq618 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) = (((X2 ◇ X0) ◇ (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) ◇ (X2 ◇ X0))) ◇ X0) := superpose eq593 eq164
  have eq624 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq593 eq399
  have eq645 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) = ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq601 eq88
  have eq646 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) = ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq40 eq645
  have eq657 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq535 eq646
  have eq660 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq657 eq67
  have eq665 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X0 := superpose eq542 eq602
  have eq666 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq665 eq84
  have eq669 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = ((X1 ◇ X3) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3))) := superpose eq665 eq86
  have eq676 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (((X3 ◇ X1) ◇ X0) ◇ X1)) := superpose eq665 eq136
  have eq677 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = (((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq666 eq64
  have eq723 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq660
  have eq782 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) := superpose eq624 eq624
  have eq841 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq624 eq782
  have eq848 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X4))) = (((X1 ◇ X4) ◇ ((X1 ◇ X4) ◇ (X1 ◇ X4))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq841 eq245
  have eq922 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (((X0 ◇ X1) ◇ X2) ◇ X4))) = (X1 ◇ X4) := superpose eq624 eq848
  have eq923 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq922 eq669
  have eq949 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose eq923 eq156
  have eq969 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq949 eq665
  have eq975 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X0)))) := superpose eq949 eq617
  have eq981 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq969 eq723
  have eq990 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq969 eq677
  have eq994 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (((X3 ◇ X1) ◇ X0) ◇ X1)) = (((((X3 ◇ X1) ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0))) := superpose eq969 eq134
  have eq999 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = (X0 ◇ X0) := superpose eq923 eq990
  have eq1025 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq999 eq676
  have eq1034 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) := superpose eq999 eq618
  have eq1068 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0))) := superpose eq999 eq994
  have eq1069 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0))) := superpose eq981 eq1068
  have eq1070 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq923 eq1069
  have eq1072 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq1070 eq1025
  have eq1073 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) := superpose eq1034 eq975
  have eq1074 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq447 eq1073
  have eq1076 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq1074 eq1072
  have eq1273 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ ((X3 ◇ X1) ◇ X0)) ◇ X0) = X0 := superpose eq1074 eq1076
  have eq1274 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq1074 eq1273
  have eq1275 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq1074 eq1274
  have eq1293 (X0 X1 : G) : X0 = X1 := superpose eq1275 eq1074
  have eq1307 (X0 : G) : sK0 ≠ X0 := superpose eq1293 eq8
  subsumption eq1307 eq1293


@[equational_result]
theorem Equation22498_implies_Equation2 (G : Type*) [Magma G] (h : Equation22498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X0) = (X0 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) ◇ (X0 ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq10
  have eq26 (X0 X1 X4 : G) : (X0 ◇ X1) = ((X4 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X1) := superpose eq10 eq12
  have eq37 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X4)) := superpose eq12 eq7
  have eq47 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X3)) = X1 := superpose eq17 eq7
  have eq85 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) = ((X4 ◇ (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) ◇ X4)) ◇ X0) := superpose eq7 eq11
  have eq97 (X0 X1 X2 X3 X5 : G) : (X1 ◇ X3) = (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X5)) := superpose eq11 eq10
  have eq98 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) := superpose eq11 eq12
  have eq112 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) = (((X2 ◇ (X0 ◇ X2)) ◇ X4) ◇ X0) := superpose eq97 eq85
  have eq113 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) := superpose eq98 eq112
  have eq115 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq113 eq37
  have eq116 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := superpose eq47 eq115
  have eq120 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq116 eq26
  have eq128 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq17 eq120
  have eq150 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq128 eq7
  have eq179 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq150 eq150
  have eq203 (X0 X4 : G) : X0 = X4 := superpose eq150 eq179
  have eq271 (X0 : G) : sK0 ≠ X0 := superpose eq203 eq8
  subsumption eq271 eq203


@[equational_result]
theorem Equation22500_implies_Equation2 (G : Type*) [Magma G] (h : Equation22500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq11
  have eq14 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) := superpose eq11 eq11
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = (((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq11 eq7
  have eq19 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) := superpose eq13 eq14
  have eq27 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ X0)) ◇ (X4 ◇ X0)) = X3 := superpose eq10 eq10
  have eq28 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X0) = X3 := superpose eq7 eq10
  have eq39 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq27 eq27
  have eq56 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq39 eq18
  have eq59 (X0 X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X0) = X3 := superpose eq56 eq28
  have eq91 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq27 eq59
  have eq108 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) := superpose eq91 eq19
  have eq109 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X2 := superpose eq59 eq108
  have eq114 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = X0 := superpose eq109 eq7
  have eq133 (X0 X3 : G) : X0 = X3 := superpose eq114 eq114
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq133 eq8
  subsumption eq135 eq133


@[equational_result]
theorem Equation22502_implies_Equation2 (G : Type*) [Magma G] (h : Equation22502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq7 eq12
  have eq41 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq12 eq17
  have eq141 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq271 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq271 eq141


@[equational_result]
theorem Equation22506_implies_Equation2 (G : Type*) [Magma G] (h : Equation22506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X2) = (X0 ◇ ((X3 ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq7 eq20
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq161 eq51


@[equational_result]
theorem Equation22508_implies_Equation2 (G : Type*) [Magma G] (h : Equation22508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) = X4 := superpose eq7 eq7
  have eq28 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq11
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq28
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq116 eq36


@[equational_result]
theorem Equation22509_implies_Equation2 (G : Type*) [Magma G] (h : Equation22509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq7 eq12
  have eq22 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq12 eq16
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) = X0 := superpose eq22 eq7
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq22 eq26
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq22 eq33
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq37 eq35


@[equational_result]
theorem Equation22510_implies_Equation2 (G : Type*) [Magma G] (h : Equation22510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq12 eq12
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq152 eq67


@[equational_result]
theorem Equation22511_implies_Equation2 (G : Type*) [Magma G] (h : Equation22511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation22513_implies_Equation2 (G : Type*) [Magma G] (h : Equation22513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X1) := superpose eq7 eq12
  have eq51 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) ◇ X3)) := superpose eq29 eq7
  have eq56 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) = (X0 ◇ (((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) ◇ (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3))) ◇ (X2 ◇ (X0 ◇ X4)))) := superpose eq7 eq9
  have eq77 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := superpose eq9 eq10
  have eq91 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq77
  have eq115 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) := superpose eq91 eq56
  have eq119 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq115 eq51
  have eq131 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X0 := superpose eq7 eq119
  have eq132 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ X1) := superpose eq131 eq29
  have eq146 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq132
  have eq183 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq146 eq9
  have eq270 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq7 eq183
  have eq426 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq270 eq270
  have eq461 (X0 X3 : G) : X0 = X3 := superpose eq7 eq426
  have eq568 (X0 : G) : sK0 ≠ X0 := superpose eq461 eq8
  subsumption eq568 eq461


@[equational_result]
theorem Equation22514_implies_Equation2 (G : Type*) [Magma G] (h : Equation22514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq11 eq7
  have eq39 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq11 eq25
  have eq103 (X0 X1 : G) : X0 = X1 := superpose eq7 eq39
  have eq214 (X0 : G) : sK0 ≠ X0 := superpose eq103 eq8
  subsumption eq214 eq103


@[equational_result]
theorem Equation22515_implies_Equation2 (G : Type*) [Magma G] (h : Equation22515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X3))) ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ (X0 ◇ X5)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq12
  have eq21 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X0 ◇ X5)) := superpose eq13 eq9
  have eq39 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq7 eq21
  have eq68 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq39 eq39
  have eq118 (X0 X4 : G) : X0 = X4 := superpose eq7 eq68
  have eq194 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq194 eq118


@[equational_result]
theorem Equation22517_implies_Equation2 (G : Type*) [Magma G] (h : Equation22517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) = (X0 ◇ (((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) ◇ (X2 ◇ (X0 ◇ X4))) ◇ (X2 ◇ (X0 ◇ X4)))) := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X4 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (((X1 ◇ X0) ◇ X4) ◇ X4)) := superpose eq7 eq9
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X0 ◇ (X1 ◇ X2)) ◇ (((X3 ◇ X4) ◇ ((X4 ◇ X5) ◇ X1)) ◇ ((X4 ◇ X5) ◇ X1))) := superpose eq9 eq14
  have eq50 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ X0) ◇ X0)) := superpose eq10 eq14
  have eq61 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X4))) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) := superpose eq14 eq9
  have eq62 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (((((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq14 eq9
  have eq71 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ X5))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ X5)))) := superpose eq14 eq10
  have eq87 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq7 eq11
  have eq94 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq11 eq9
  have eq108 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = (X0 ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X2 ◇ (X0 ◇ X3)))) := superpose eq7 eq50
  have eq114 (X0 X1 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := superpose eq7 eq50
  have eq120 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq50
  have eq121 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X4))) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) := superpose eq14 eq50
  have eq127 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) := superpose eq50 eq14
  have eq147 (X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X4))) = (X2 ◇ X1) := superpose eq127 eq121
  have eq153 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0))) := superpose eq147 eq94
  have eq156 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1))) := superpose eq147 eq87
  have eq159 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) = (X0 ◇ (((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) ◇ X0) ◇ (X2 ◇ (X0 ◇ X4)))) := superpose eq147 eq12
  have eq165 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = (X0 ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ (X2 ◇ (X0 ◇ X3)))) := superpose eq147 eq108
  have eq168 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ X5)))) := superpose eq147 eq71
  have eq177 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq147 eq62
  have eq194 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2))) := superpose eq147 eq61
  have eq210 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0))) := superpose eq147 eq153
  have eq218 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) := superpose eq147 eq159
  have eq233 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq147 eq165
  have eq236 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq233 eq120
  have eq238 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1))) := superpose eq233 eq156
  have eq239 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0))) := superpose eq233 eq210
  have eq242 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := superpose eq233 eq114
  have eq248 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4))))) := superpose eq147 eq168
  have eq249 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))) ◇ X3)) := superpose eq147 eq248
  have eq250 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ (X1 ◇ X4))) ◇ (((X0 ◇ X1) ◇ X3) ◇ X3)) := superpose eq147 eq249
  have eq251 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ (((X0 ◇ X1) ◇ X3) ◇ X3)) := superpose eq147 eq250
  have eq256 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq147 eq177
  have eq265 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq251 eq194
  have eq266 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X2 ◇ X1) := superpose eq265 eq256
  have eq270 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq266 eq239
  have eq271 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq266 eq238
  have eq273 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X0 ◇ (X1 ◇ X2)) ◇ (((X4 ◇ X5) ◇ (X3 ◇ X4)) ◇ ((X4 ◇ X5) ◇ X1))) := superpose eq266 eq49
  have eq282 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq266 eq236
  have eq315 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq266 eq270
  have eq316 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq266 eq315
  have eq317 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq266 eq316
  have eq318 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq266 eq317
  have eq319 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4)) ◇ (X1 ◇ X0)) := superpose eq266 eq271
  have eq320 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (((((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq266 eq319
  have eq321 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) ◇ (X1 ◇ X0)) := superpose eq266 eq320
  have eq322 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq218 eq321
  have eq323 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X1 ◇ (X0 ◇ X1)) := superpose eq266 eq322
  have eq324 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) := superpose eq266 eq323
  have eq325 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq266 eq324
  have eq326 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq325 eq318
  have eq329 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X3)) = X0 := superpose eq326 eq242
  have eq345 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X0 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X5)) := superpose eq329 eq273
  have eq346 (X0 X1 X3 X4 X5 : G) : (X3 ◇ X4) = ((X1 ◇ X0) ◇ (X4 ◇ X5)) := superpose eq266 eq345
  have eq359 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq329 eq282
  have eq360 (X3 X4 : G) : (X3 ◇ X4) = X4 := superpose eq359 eq346
  have eq372 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq360 eq329
  have eq376 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq360 eq372
  have eq385 (X0 X3 : G) : X0 = X3 := superpose eq376 eq376
  have eq396 (X0 : G) : sK0 ≠ X0 := superpose eq385 eq8
  subsumption eq396 eq385


@[equational_result]
theorem Equation22519_implies_Equation2 (G : Type*) [Magma G] (h : Equation22519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq12 eq12
  have eq68 (X0 X1 : G) : X0 = X1 := superpose eq12 eq17
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq124 eq68


@[equational_result]
theorem Equation22521_implies_Equation2 (G : Type*) [Magma G] (h : Equation22521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) = X2 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq7 eq10
  have eq51 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X1) = X3 := superpose eq10 eq11
  have eq66 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq24 eq51
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq7 eq66
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq141 eq67


@[equational_result]
theorem Equation22522_implies_Equation2 (G : Type*) [Magma G] (h : Equation22522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2))) = X0 := superpose eq7 eq9
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq9 eq9
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) = (X0 ◇ (((X0 ◇ X2) ◇ X2) ◇ ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3))) := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X4)) = ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X4) ◇ X4))) := superpose eq10 eq10
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq10 eq10
  have eq34 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) = X4 := superpose eq10 eq7
  have eq39 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1)))) := superpose eq18 eq12
  have eq43 (X0 X2 X3 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq7 eq27
  have eq90 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq43 eq11
  have eq91 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X4)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq43 eq21
  have eq96 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq43 eq39
  have eq104 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X1)) = X4 := superpose eq43 eq34
  have eq109 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = (X3 ◇ (X1 ◇ X4)) := superpose eq43 eq91
  have eq110 (X1 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = X1 := superpose eq90 eq109
  have eq114 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq110 eq90
  have eq118 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq110 eq96
  have eq134 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X1)) = X4 := superpose eq118 eq104
  have eq135 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X1 ◇ X2))) ◇ X0) = X4 := superpose eq118 eq134
  have eq136 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq118 eq135
  have eq137 (X0 X1 : G) : X0 = X1 := superpose eq114 eq136
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq137 eq8
  subsumption eq145 eq137


@[equational_result]
theorem Equation22523_implies_Equation2 (G : Type*) [Magma G] (h : Equation22523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq122 eq36


@[equational_result]
theorem Equation22525_implies_Equation2 (G : Type*) [Magma G] (h : Equation22525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (X0 ◇ (((X0 ◇ X3) ◇ X4) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X3 : G) : (X0 ◇ X3) = (X0 ◇ X1) := superpose eq7 eq12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X5))) ◇ (X0 ◇ X6)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq10 eq7
  have eq47 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X4) = X0 := superpose eq7 eq20
  have eq93 (X0 X1 X2 X4 : G) : (X4 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq47 eq45
  have eq185 (X0 X1 : G) : X0 = X1 := superpose eq12 eq93
  have eq290 (X0 : G) : sK0 ≠ X0 := superpose eq185 eq8
  subsumption eq290 eq185


@[equational_result]
theorem Equation22526_implies_Equation2 (G : Type*) [Magma G] (h : Equation22526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) ◇ X0) = X2 := superpose eq7 eq7
  have eq34 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq34
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq138 eq44


@[equational_result]
theorem Equation22527_implies_Equation2 (G : Type*) [Magma G] (h : Equation22527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X5) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ X3) = (X0 ◇ (((X0 ◇ X3) ◇ X4) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) ◇ (X0 ◇ ((X0 ◇ X5) ◇ X5))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) := superpose eq7 eq10
  have eq17 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X4) ◇ X4))) = X0 := superpose eq10 eq7
  have eq59 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X0 ◇ X5)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X3)))) = X0 := superpose eq14 eq7
  have eq107 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X3 ◇ ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X6)) = ((X7 ◇ ((X3 ◇ ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X6)) ◇ X8)) ◇ ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X9) ◇ X9))))) := superpose eq11 eq11
  have eq113 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) = ((X5 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X6) ◇ X6)))) := superpose eq11 eq9
  have eq127 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X4)) = X0 := superpose eq59 eq113
  have eq128 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (X3 ◇ ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X6)) = ((X7 ◇ ((X3 ◇ ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X6)) ◇ X8)) ◇ X0) := superpose eq127 eq107
  have eq140 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ X0) = (X3 ◇ ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X6)) := superpose eq127 eq128
  have eq141 (X0 X3 X6 : G) : (X3 ◇ X0) = (X3 ◇ (X0 ◇ X6)) := superpose eq127 eq140
  have eq150 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X4))) = X0 := superpose eq141 eq17
  have eq164 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X4)) = X0 := superpose eq141 eq127
  have eq191 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq141 eq150
  have eq192 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq141 eq191
  have eq193 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq141 eq192
  have eq229 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq10 eq141
  have eq234 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq164 eq229
  have eq235 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq234 eq193
  have eq250 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq234 eq235
  have eq251 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq234 eq250
  have eq257 (X0 X1 : G) : X0 = X1 := superpose eq251 eq234
  have eq271 (X0 : G) : sK0 ≠ X0 := superpose eq257 eq8
  subsumption eq271 eq257


@[equational_result]
theorem Equation22528_implies_Equation2 (G : Type*) [Magma G] (h : Equation22528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq12
  have eq40 (X0 X5 : G) : X0 = X5 := superpose eq7 eq18
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq128 eq40


@[equational_result]
theorem Equation22530_implies_Equation2 (G : Type*) [Magma G] (h : Equation22530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq7 eq9
  have eq32 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq10 eq9
  have eq35 (X0 X1 X2 X4 : G) : (X2 ◇ (X0 ◇ X1)) = ((X4 ◇ X1) ◇ ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X4)) := superpose eq10 eq9
  have eq40 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq32 eq10
  have eq70 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq40 eq9
  have eq71 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq40 eq7
  have eq89 (X0 X1 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq71 eq16
  have eq160 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) := superpose eq89 eq7
  have eq210 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq70 eq71
  have eq234 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ (X0 ◇ X2))) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq7 eq160
  have eq386 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq40 eq234
  have eq388 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq89 eq234
  have eq459 (X0 X1 X3 : G) : ((X3 ◇ X1) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := superpose eq7 eq35
  have eq481 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq89 eq35
  have eq528 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq40 eq459
  have eq540 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq459 eq459
  have eq615 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq540 eq481
  have eq642 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq615 eq388
  have eq787 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq642 eq642
  have eq846 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq642 eq787
  have eq848 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq846 eq386
  have eq927 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq528 eq848
  have eq928 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq927 eq210
  have eq1177 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq927 eq928
  have eq1178 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X1 := superpose eq927 eq1177
  have eq1179 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq927 eq1178
  have eq1180 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq927 eq1179
  have eq1193 (X0 X2 : G) : X0 = X2 := superpose eq1180 eq1180
  have eq1211 (X0 : G) : sK0 ≠ X0 := superpose eq1193 eq8
  subsumption eq1211 eq1193


@[equational_result]
theorem Equation22532_implies_Equation2 (G : Type*) [Magma G] (h : Equation22532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ X3) = (((X1 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X3) ◇ X4)) ◇ (X0 ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : ((X4 ◇ (X0 ◇ X5)) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq12
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((X3 ◇ X0) ◇ X1) := superpose eq7 eq12
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X1) := superpose eq7 eq12
  have eq23 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X4)) := superpose eq17 eq10
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq23 eq12
  have eq54 (X0 X1 X4 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X4)) := superpose eq37 eq23
  have eq64 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq17 eq7
  have eq79 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ X3) ◇ ((X0 ◇ X0) ◇ X4)) = X0 := superpose eq7 eq54
  have eq80 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X4)) := superpose eq12 eq54
  have eq95 (X0 X1 X2 X3 X5 : G) : (X1 ◇ X0) = ((X5 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1) := superpose eq7 eq15
  have eq104 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X5 ◇ X0) ◇ (X4 ◇ X2)) := superpose eq15 eq15
  have eq153 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X5 ◇ X0)) := superpose eq95 eq9
  have eq165 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X5 ◇ (X4 ◇ X1)) ◇ (X6 ◇ (X4 ◇ X1))) := superpose eq15 eq153
  have eq167 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X1)) = ((X3 ◇ X1) ◇ (X4 ◇ X1)) := superpose eq17 eq153
  have eq172 (X0 X1 X4 X5 : G) : ((X4 ◇ (X1 ◇ X0)) ◇ (X5 ◇ (X1 ◇ X0))) = X0 := superpose eq7 eq153
  have eq244 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq172 eq165
  have eq245 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq244 eq37
  have eq252 (X0 X1 X4 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X4)) := superpose eq245 eq80
  have eq256 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ X0) ◇ X3) = (((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ (X0 ◇ X5)) := superpose eq252 eq11
  have eq262 (X0 X1 X4 X5 : G) : ((X4 ◇ (X0 ◇ X5)) ◇ (X1 ◇ X0)) = X0 := superpose eq252 eq13
  have eq283 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ X0) ◇ X3) = (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X5)) := superpose eq252 eq256
  have eq284 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ X0) ◇ X3) = (((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X5)) := superpose eq17 eq283
  have eq285 (X0 X1 X3 X5 : G) : ((X1 ◇ X0) ◇ X3) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X5)) := superpose eq252 eq284
  have eq286 (X0 X1 X3 X5 : G) : ((X1 ◇ X0) ◇ X3) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X5)) := superpose eq17 eq285
  have eq287 (X0 X1 X3 X5 : G) : ((X1 ◇ X0) ◇ X3) = ((X1 ◇ X1) ◇ (X0 ◇ X5)) := superpose eq252 eq286
  have eq291 (X0 X1 X4 : G) : ((X4 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq252 eq262
  have eq292 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq291 eq167
  have eq294 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq292 eq104
  have eq297 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq294 eq287
  have eq298 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X0) = X0 := superpose eq297 eq79
  have eq300 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq297 eq64
  have eq311 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq297 eq298
  have eq312 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq297 eq300
  have eq318 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X4)) = X1 := superpose eq312 eq252
  have eq323 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq312 eq318
  have eq324 (X0 X1 : G) : X0 = X1 := superpose eq311 eq323
  have eq332 (X0 : G) : sK0 ≠ X0 := superpose eq324 eq8
  subsumption eq332 eq324


@[equational_result]
theorem Equation22534_implies_Equation2 (G : Type*) [Magma G] (h : Equation22534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) = (X0 ◇ (((X2 ◇ (X0 ◇ X4)) ◇ (X2 ◇ (X0 ◇ X4))) ◇ (X2 ◇ (X0 ◇ X4)))) := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) = X3 := superpose eq9 eq7
  have eq33 (X1 X2 X3 : G) : (X2 ◇ X2) = (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) := superpose eq10 eq17
  have eq41 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq22 eq29
  have eq42 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq41 eq10
  have eq50 (X1 X2 X3 : G) : (X2 ◇ X2) = (X1 ◇ ((X2 ◇ X2) ◇ X3)) := superpose eq42 eq33
  have eq55 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq22 eq50
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq55 eq42
  have eq63 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = X3 := superpose eq56 eq41
  have eq69 (X0 X3 X4 : G) : (X4 ◇ X0) = X3 := superpose eq56 eq63
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq69 eq69
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq78 eq70


@[equational_result]
theorem Equation22535_implies_Equation2 (G : Type*) [Magma G] (h : Equation22535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1))) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2)) = X0 := superpose eq7 eq9
  have eq54 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ X2) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq18 eq9
  have eq63 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq18 eq11
  have eq65 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq9 eq11
  have eq85 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq65 eq9
  have eq86 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq65 eq18
  have eq89 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq65 eq7
  have eq98 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq89
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq98 eq54
  have eq105 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq98 eq86
  have eq111 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) = X2 := superpose eq105 eq11
  have eq123 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq105 eq85
  have eq125 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq105 eq63
  have eq178 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq105 eq123
  have eq181 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq105 eq125
  have eq182 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X2 ◇ X1)) := superpose eq181 eq178
  have eq184 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = ((X0 ◇ X2) ◇ X1) := superpose eq182 eq101
  have eq192 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq182 eq111
  have eq210 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = X2 := superpose eq184 eq192
  have eq211 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X2 := superpose eq182 eq210
  have eq222 (X0 X3 : G) : X0 = X3 := superpose eq211 eq211
  have eq224 (X0 : G) : sK0 ≠ X0 := superpose eq222 eq8
  subsumption eq224 eq222


@[equational_result]
theorem Equation22536_implies_Equation2 (G : Type*) [Magma G] (h : Equation22536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq11 eq11
  have eq43 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2))) ◇ X3) = X5 := superpose eq9 eq11
  have eq66 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq17 eq43
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq66
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq141 eq67


@[equational_result]
theorem Equation22540_implies_Equation2 (G : Type*) [Magma G] (h : Equation22540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4))) ◇ (X0 ◇ X5)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X2 ◇ X3)) := superpose eq7 eq12
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X4))) ◇ (X0 ◇ X5)) = X3 := superpose eq15 eq11
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X4))) ◇ (X0 ◇ X5)) = X3 := superpose eq15 eq23
  have eq25 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ (X2 ◇ (X2 ◇ X4))) ◇ (X0 ◇ X5)) = X3 := superpose eq15 eq24
  have eq37 (X0 X1 : G) : X0 = X1 := superpose eq7 eq25
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq47 eq37


@[equational_result]
theorem Equation22542_implies_Equation2 (G : Type*) [Magma G] (h : Equation22542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = (X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X4) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq65 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ X1) := superpose eq10 eq10
  have eq86 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X4) = X0 := superpose eq7 eq65
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq86 eq11
  have eq159 (X0 X4 : G) : X0 = X4 := superpose eq134 eq134
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq159 eq8
  subsumption eq188 eq159


@[equational_result]
theorem Equation22543_implies_Equation2 (G : Type*) [Magma G] (h : Equation22543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X0 ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4))) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X5) = X2 := superpose eq7 eq12
  have eq24 (X0 X3 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X3 := superpose eq15 eq11
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq24
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq55 eq31


@[equational_result]
theorem Equation22544_implies_Equation2 (G : Type*) [Magma G] (h : Equation22544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X5) ◇ X5))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X4)) := superpose eq7 eq12
  have eq16 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X4)) = X1 := superpose eq12 eq12
  have eq23 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq16 eq15
  have eq24 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X5) ◇ X5))) = X3 := superpose eq23 eq11
  have eq31 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq23 eq24
  have eq32 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq23 eq31
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq32 eq32
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq35 eq33


@[equational_result]
theorem Equation22545_implies_Equation2 (G : Type*) [Magma G] (h : Equation22545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X7 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X0 ◇ X7)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X7 : G) : (X0 ◇ (X0 ◇ X7)) = X3 := superpose eq12 eq11
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation22547_implies_Equation2 (G : Type*) [Magma G] (h : Equation22547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X0))))) := superpose eq7 eq10
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0))) = ((X2 ◇ (((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq10 eq7
  have eq24 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ ((((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0))) ◇ X1) ◇ X2)) = X1 := superpose eq10 eq7
  have eq25 (X0 X1 X2 X3 : G) : ((((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq10 eq7
  have eq37 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0))) = ((X2 ◇ (X1 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0))))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq21 eq23
  have eq38 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0))) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq10 eq37
  have eq39 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0)))) ◇ X2)) = X1 := superpose eq21 eq24
  have eq40 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = X1 := superpose eq10 eq39
  have eq41 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0))) = X1 := superpose eq40 eq38
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := superpose eq41 eq15
  have eq48 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq43 eq25
  have eq49 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X2 := superpose eq41 eq48
  have eq52 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq49 eq11
  have eq90 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ X3) ◇ X5)) = (((X0 ◇ X1) ◇ X2) ◇ X4) := superpose eq52 eq52
  have eq96 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq7 eq52
  have eq137 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X4) = X1 := superpose eq96 eq90
  have eq381 (X0 X2 : G) : X0 = X2 := superpose eq7 eq137
  have eq409 (X0 : G) : sK0 ≠ X0 := superpose eq381 eq8
  subsumption eq409 eq381


@[equational_result]
theorem Equation22548_implies_Equation2 (G : Type*) [Magma G] (h : Equation22548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) ◇ X1) := superpose eq10 eq12
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ X0) := superpose eq12 eq12
  have eq31 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq12 eq7
  have eq40 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq7 eq31
  have eq46 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X1 := superpose eq12 eq31
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) ◇ X1) := superpose eq46 eq19
  have eq60 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X3) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq46 eq40
  have eq64 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X2)))) := superpose eq46 eq11
  have eq72 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((X3 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (((X2 ◇ X0) ◇ X2) ◇ (X4 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq7 eq64
  have eq82 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X0)))) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ (X3 ◇ (X1 ◇ X0))) ◇ (X5 ◇ ((X1 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X2)))) := superpose eq64 eq64
  have eq84 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ (X3 ◇ (X5 ◇ (X3 ◇ X4)))) := superpose eq64 eq64
  have eq97 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq64
  have eq125 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((X3 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq46 eq72
  have eq131 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X0)))) ◇ X2) = X1 := superpose eq46 eq82
  have eq140 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) := superpose eq97 eq26
  have eq152 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq46 eq140
  have eq153 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) := superpose eq152 eq10
  have eq157 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ X1) := superpose eq152 eq57
  have eq167 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = X1 := superpose eq152 eq46
  have eq177 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq152 eq97
  have eq178 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((X3 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) := superpose eq152 eq125
  have eq193 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) := superpose eq60 eq157
  have eq194 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X1) := superpose eq152 eq193
  have eq203 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq177 eq194
  have eq204 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq152 eq203
  have eq205 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq204 eq178
  have eq212 (X0 X1 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X3 ◇ (X5 ◇ (X3 ◇ X4)))) := superpose eq205 eq84
  have eq213 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X1 := superpose eq205 eq131
  have eq222 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X0 ◇ X2)) := superpose eq205 eq153
  have eq229 (X0 X1 X3 X4 : G) : ((X4 ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X3)) := superpose eq205 eq212
  have eq238 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X1 := superpose eq222 eq167
  have eq265 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ (X3 ◇ X1)) ◇ (X4 ◇ X3)) = X4 := superpose eq238 eq229
  have eq273 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq238 eq265
  have eq275 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq273 eq213
  have eq278 (X0 X3 : G) : X0 = X3 := superpose eq275 eq275
  have eq286 (X0 : G) : sK0 ≠ X0 := superpose eq278 eq8
  subsumption eq286 eq278


@[equational_result]
theorem Equation22549_implies_Equation2 (G : Type*) [Magma G] (h : Equation22549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X0) = (X0 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4)) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = ((X2 ◇ (((X3 ◇ (X0 ◇ X1)) ◇ X4) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq10 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ ((((X3 ◇ (X0 ◇ X1)) ◇ X4) ◇ X1) ◇ X5)) = X1 := superpose eq10 eq7
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = ((X2 ◇ (X1 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X4))) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq17 eq20
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq10 eq23
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X4)) ◇ X5)) = X1 := superpose eq17 eq21
  have eq26 (X0 X1 X2 X5 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X5)) = X1 := superpose eq10 eq25
  have eq27 (X0 X1 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = X1 := superpose eq26 eq24
  have eq446 (X0 X2 : G) : X0 = X2 := superpose eq7 eq27
  have eq474 (X0 : G) : sK0 ≠ X0 := superpose eq446 eq8
  subsumption eq474 eq446


@[equational_result]
theorem Equation22553_implies_Equation2 (G : Type*) [Magma G] (h : Equation22553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq12 eq12
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X4)) = ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ X5)) := superpose eq12 eq7
  have eq24 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X4)) = X2 := superpose eq18 eq21
  have eq25 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq24 eq12
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq25 eq25
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation22556_implies_Equation2 (G : Type*) [Magma G] (h : Equation22556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X2 := superpose eq10 eq11
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq10 eq10
  have eq23 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq10 eq14
  have eq24 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X2 := superpose eq23 eq13
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq24 eq24
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq51 eq37


@[equational_result]
theorem Equation22557_implies_Equation2 (G : Type*) [Magma G] (h : Equation22557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X2) = (X0 ◇ ((X3 ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq7 eq22
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq139 eq53


@[equational_result]
theorem Equation22559_implies_Equation2 (G : Type*) [Magma G] (h : Equation22559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq12 eq12
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq157 eq67


@[equational_result]
theorem Equation22560_implies_Equation2 (G : Type*) [Magma G] (h : Equation22560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X3) = (X0 ◇ ((X2 ◇ X4) ◇ X2)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq139 eq58


@[equational_result]
theorem Equation22561_implies_Equation2 (G : Type*) [Magma G] (h : Equation22561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X3) = (X0 ◇ ((X3 ◇ X4) ◇ X4)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq177 eq55


@[equational_result]
theorem Equation22562_implies_Equation2 (G : Type*) [Magma G] (h : Equation22562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq133 eq53


@[equational_result]
theorem Equation22564_implies_Equation2 (G : Type*) [Magma G] (h : Equation22564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = (X0 ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq10 eq10
  have eq152 (X0 X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ X0) := superpose eq7 eq22
  have eq253 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ X3) := superpose eq152 eq152
  have eq479 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq253
  have eq574 (X0 X3 : G) : X0 = X3 := superpose eq479 eq479
  have eq676 (X0 : G) : sK0 ≠ X0 := superpose eq574 eq8
  subsumption eq676 eq574


@[equational_result]
theorem Equation22565_implies_Equation2 (G : Type*) [Magma G] (h : Equation22565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X0) = (X0 ◇ ((X4 ◇ (X3 ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) ◇ (X0 ◇ X4)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X2) ◇ ((X4 ◇ X0) ◇ X5)) = X0 := superpose eq7 eq10
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq10
  have eq26 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = ((X4 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X3))) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq7 eq12
  have eq43 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = ((X4 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X0) ◇ X2) ◇ X3))) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq17 eq26
  have eq64 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X2) := superpose eq17 eq12
  have eq105 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) = ((X5 ◇ (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) ◇ ((X6 ◇ X0) ◇ X3))) ◇ X0) := superpose eq7 eq11
  have eq116 (X0 X1 X2 X3 X5 : G) : (X1 ◇ X3) = (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X5)) := superpose eq11 eq10
  have eq118 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) := superpose eq11 eq12
  have eq129 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = ((X4 ◇ (X0 ◇ (X0 ◇ X3))) ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq116 eq43
  have eq136 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) = (((X2 ◇ (X0 ◇ X3)) ◇ X5) ◇ X0) := superpose eq116 eq105
  have eq138 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) := superpose eq118 eq136
  have eq145 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ X2) ◇ X3) := superpose eq138 eq129
  have eq150 (X1 X3 X5 : G) : (X1 ◇ X3) = (X3 ◇ (X1 ◇ X5)) := superpose eq145 eq116
  have eq154 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X2) := superpose eq150 eq64
  have eq191 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X0 ◇ X3) ◇ X2) := superpose eq150 eq154
  have eq192 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ ((X4 ◇ X0) ◇ X5)) = X0 := superpose eq191 eq13
  have eq198 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (X5 ◇ X4)) = X0 := superpose eq191 eq192
  have eq707 (X0 X5 : G) : X0 = X5 := superpose eq198 eq198
  have eq891 (X0 : G) : sK0 ≠ X0 := superpose eq707 eq8
  subsumption eq891 eq707


@[equational_result]
theorem Equation22566_implies_Equation2 (G : Type*) [Magma G] (h : Equation22566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X5 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X3 ◇ X0) = (X0 ◇ ((X4 ◇ (X3 ◇ X0)) ◇ X4)) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq10
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X2 ◇ (((X3 ◇ (X0 ◇ X1)) ◇ X3) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq10 eq7
  have eq21 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ (X5 ◇ (X5 ◇ (X2 ◇ (X0 ◇ X3))))) := superpose eq17 eq9
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X0))) = X0 := superpose eq17 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X3) = ((X2 ◇ (((X3 ◇ (X0 ◇ X1)) ◇ X3) ◇ X4)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq19
  have eq30 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = ((X2 ◇ ((X3 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq17 eq29
  have eq33 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ X3))) = X3 := superpose eq25 eq25
  have eq49 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq17 eq33
  have eq63 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ (X0 ◇ X1))) = X0 := superpose eq49 eq30
  have eq65 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ X2) := superpose eq63 eq21
  have eq110 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X3) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq25 eq65
  have eq151 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq65 eq33
  have eq159 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq110 eq151
  have eq160 (X0 X4 : G) : X0 = X4 := superpose eq25 eq159
  have eq258 (X0 : G) : sK0 ≠ X0 := superpose eq160 eq8
  subsumption eq258 eq160


@[equational_result]
theorem Equation22567_implies_Equation2 (G : Type*) [Magma G] (h : Equation22567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X6 X7 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X6 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X7)) := superpose eq7 eq7
  have eq10 (X0 X3 X5 X6 : G) : (X3 ◇ X0) = (X0 ◇ ((X5 ◇ (X3 ◇ X0)) ◇ X6)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X7 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) ◇ (X0 ◇ X7)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X5 : G) : ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X5)) := superpose eq7 eq10
  have eq67 (X0 X1 X2 X3 X4 X7 X8 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) = (X0 ◇ ((X7 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4))) ◇ X8)) := superpose eq7 eq9
  have eq99 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) := superpose eq9 eq12
  have eq101 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq9 eq10
  have eq116 (X0 X1 X2 X3 X4 X8 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) = (X0 ◇ (X8 ◇ ((X2 ◇ X0) ◇ X3))) := superpose eq99 eq67
  have eq117 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X0) = (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) := superpose eq101 eq116
  have eq118 (X0 X2 X3 X7 : G) : ((X2 ◇ X0) ◇ X3) = ((X2 ◇ X0) ◇ (X0 ◇ X7)) := superpose eq117 eq11
  have eq143 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := superpose eq7 eq15
  have eq209 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X1)) ◇ X5) = ((X3 ◇ (X4 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq15 eq118
  have eq223 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X6)) = X4 := superpose eq118 eq7
  have eq273 (X1 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X1)) ◇ X5) = X1 := superpose eq143 eq209
  have eq285 (X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X5)) ◇ X2) = X4 := superpose eq273 eq223
  have eq626 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq285 eq285
  have eq679 (X0 X3 : G) : X0 = X3 := superpose eq626 eq626
  have eq849 (X0 : G) : sK0 ≠ X0 := superpose eq679 eq8
  subsumption eq849 eq679


@[equational_result]
theorem Equation22569_implies_Equation2 (G : Type*) [Magma G] (h : Equation22569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X5 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq7 eq9
  have eq46 (X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) ◇ X1) = X3 := superpose eq28 eq11
  have eq61 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ X4) ◇ X4) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X0))) ◇ X3) = X5 := superpose eq9 eq46
  have eq77 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq28 eq61
  have eq78 (X0 X4 : G) : X0 = X4 := superpose eq7 eq77
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq161 eq78


@[equational_result]
theorem Equation22570_implies_Equation2 (G : Type*) [Magma G] (h : Equation22570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = (X0 ◇ ((X4 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) ◇ (X0 ◇ X5)) = X4 := superpose eq7 eq7
  have eq57 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq10 eq11
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq57
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq159 eq68


@[equational_result]
theorem Equation22571_implies_Equation2 (G : Type*) [Magma G] (h : Equation22571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ ((X5 ◇ X1) ◇ X5)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq7 eq9
  have eq92 (X0 X3 : G) : X0 = X3 := superpose eq7 eq25
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq173 eq92


@[equational_result]
theorem Equation22572_implies_Equation2 (G : Type*) [Magma G] (h : Equation22572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X3 ◇ X1) = (X0 ◇ X1) := superpose eq7 eq12
  have eq70 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq12 eq17
  have eq187 (X0 X5 : G) : X0 = X5 := superpose eq7 eq70
  have eq328 (X0 : G) : sK0 ≠ X0 := superpose eq187 eq8
  subsumption eq328 eq187


@[equational_result]
theorem Equation22574_implies_Equation2 (G : Type*) [Magma G] (h : Equation22574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X2) = (X0 ◇ ((X4 ◇ X1) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X3 ◇ X0) := superpose eq7 eq10
  have eq70 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq25
  have eq168 (X0 X4 : G) : X0 = X4 := superpose eq7 eq70
  have eq310 (X0 : G) : sK0 ≠ X0 := superpose eq168 eq8
  subsumption eq310 eq168


@[equational_result]
theorem Equation22575_implies_Equation2 (G : Type*) [Magma G] (h : Equation22575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = (X0 ◇ ((X4 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq80 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq164 eq80


@[equational_result]
theorem Equation22576_implies_Equation2 (G : Type*) [Magma G] (h : Equation22576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = (X0 ◇ ((X4 ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq181 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq181 eq57


@[equational_result]
theorem Equation22577_implies_Equation2 (G : Type*) [Magma G] (h : Equation22577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X3 ◇ X2) = (X0 ◇ ((X5 ◇ X4) ◇ X6)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq22
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq140 eq57


@[equational_result]
theorem Equation22579_implies_Equation2 (G : Type*) [Magma G] (h : Equation22579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq18 eq12
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22580_implies_Equation2 (G : Type*) [Magma G] (h : Equation22580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X3) = (X0 ◇ ((X4 ◇ X4) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq11 eq19
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq182 eq58


@[equational_result]
theorem Equation22581_implies_Equation2 (G : Type*) [Magma G] (h : Equation22581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X3 ◇ X3) = (X0 ◇ ((X4 ◇ X4) ◇ X4)) := superpose eq7 eq7
  have eq21 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq57 (X0 X2 : G) : X0 = X2 := superpose eq7 eq21
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq159 eq57


@[equational_result]
theorem Equation22582_implies_Equation2 (G : Type*) [Magma G] (h : Equation22582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation22584_implies_Equation2 (G : Type*) [Magma G] (h : Equation22584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) ◇ X0) = X4 := superpose eq7 eq7
  have eq33 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq12
  have eq42 (X0 X5 : G) : X0 = X5 := superpose eq7 eq33
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq147 eq42


@[equational_result]
theorem Equation22585_implies_Equation2 (G : Type*) [Magma G] (h : Equation22585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X3 ◇ X4) = (X0 ◇ ((X5 ◇ X6) ◇ X2)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq22
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq133 eq57


@[equational_result]
theorem Equation22586_implies_Equation2 (G : Type*) [Magma G] (h : Equation22586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq157 eq53


@[equational_result]
theorem Equation22587_implies_Equation2 (G : Type*) [Magma G] (h : Equation22587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 X6 : G) : (X3 ◇ X4) = (X0 ◇ ((X5 ◇ X6) ◇ X6)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq22
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq165 eq57


@[equational_result]
theorem Equation22588_implies_Equation2 (G : Type*) [Magma G] (h : Equation22588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq12
  have eq53 (X0 X6 : G) : X0 = X6 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation22594_implies_Equation2 (G : Type*) [Magma G] (h : Equation22594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X0)) = ((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X1) := superpose eq11 eq11
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)))) ◇ (X0 ◇ X2)) := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2)) = X1 := superpose eq11 eq7
  have eq39 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X1 ◇ X0)))) = (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X1 ◇ X0)))))) ◇ (X0 ◇ X3)) := superpose eq7 eq12
  have eq93 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))))) = (((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))))))) ◇ (X1 ◇ X3)) := superpose eq10 eq13
  have eq118 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))))) = (((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))))))) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X4)) := superpose eq10 eq15
  have eq120 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = ((((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq15 eq15
  have eq129 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) := superpose eq15 eq13
  have eq130 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) := superpose eq15 eq11
  have eq149 (X0 X1 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1)) = X0 := superpose eq11 eq16
  have eq151 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ ((((X1 ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))))) ◇ X3)) := superpose eq12 eq16
  have eq208 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))))))) ◇ X1)) := superpose eq15 eq149
  have eq210 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq149 eq149
  have eq235 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0))) ◇ X1)) = X0 := superpose eq210 eq208
  have eq241 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ X1)) = X0 := superpose eq11 eq235
  have eq242 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq11 eq241
  have eq243 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq242 eq149
  have eq247 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X4)) := superpose eq243 eq118
  have eq248 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X3)) := superpose eq243 eq93
  have eq249 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X3)) := superpose eq243 eq39
  have eq250 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3)) := superpose eq243 eq151
  have eq255 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq243 eq130
  have eq256 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq243 eq129
  have eq257 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq243 eq120
  have eq378 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq243 eq247
  have eq379 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X3) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) := superpose eq243 eq378
  have eq380 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X3) ◇ (((X1 ◇ X0) ◇ X2) ◇ X4)) = X0 := superpose eq243 eq379
  have eq381 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X3)) := superpose eq243 eq248
  have eq382 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) := superpose eq243 eq381
  have eq383 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) = X0 := superpose eq243 eq382
  have eq384 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = (X1 ◇ (X0 ◇ X3)) := superpose eq243 eq249
  have eq385 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) := superpose eq243 eq250
  have eq386 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X3)) := superpose eq243 eq385
  have eq399 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq243 eq255
  have eq400 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq243 eq399
  have eq401 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq243 eq256
  have eq402 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq243 eq401
  have eq403 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq243 eq402
  have eq404 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq403 eq400
  have eq406 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq383 eq257
  have eq407 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq383 eq406
  have eq408 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X1 := superpose eq407 eq384
  have eq409 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X2) := superpose eq408 eq386
  have eq413 (X0 X1 X3 X4 : G) : ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) = X0 := superpose eq409 eq380
  have eq417 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ (X1 ◇ X0)) = X0 := superpose eq409 eq413
  have eq418 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq417 eq404
  have eq419 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq418 eq403
  have eq428 (X0 X1 : G) : X0 = X1 := superpose eq418 eq419
  have eq438 (X0 : G) : sK0 ≠ X0 := superpose eq428 eq8
  subsumption eq438 eq428


@[equational_result]
theorem Equation22596_implies_Equation2 (G : Type*) [Magma G] (h : Equation22596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq10
  have eq15 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq7
  have eq19 (X0 X2 : G) : (((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X2 := superpose eq10 eq12
  have eq35 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) ◇ X0) := superpose eq14 eq12
  have eq37 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq14 eq35
  have eq41 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq14 eq11
  have eq47 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq14 eq11
  have eq48 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq11 eq11
  have eq70 (X0 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) = X0 := superpose eq14 eq15
  have eq86 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq41 eq70
  have eq87 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose eq86 eq47
  have eq88 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq86 eq87
  have eq89 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq88 eq37
  have eq94 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq88 eq14
  have eq98 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq94 eq89
  have eq99 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X0 := superpose eq94 eq10
  have eq113 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq94 eq99
  have eq114 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq98 eq113
  have eq116 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq114 eq48
  have eq118 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq114 eq19
  have eq142 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq114 eq116
  have eq143 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) = X1 := superpose eq114 eq142
  have eq146 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq118 eq98
  have eq148 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X2))) = X1 := superpose eq146 eq143
  have eq153 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq146 eq148
  have eq154 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq146 eq153
  have eq155 (X0 X1 : G) : X0 = X1 := superpose eq94 eq154
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq155 eq8
  subsumption eq160 eq155


@[equational_result]
theorem Equation22598_implies_Equation2 (G : Type*) [Magma G] (h : Equation22598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq10 eq12
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq36 eq28


@[equational_result]
theorem Equation22601_implies_Equation2 (G : Type*) [Magma G] (h : Equation22601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = (((X3 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X2))) := superpose eq9 eq9
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X4) = (((X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq9
  have eq27 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq9 eq9
  have eq32 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X3) ◇ X4)) = X3 := superpose eq9 eq7
  have eq43 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X3) = X0 := superpose eq7 eq27
  have eq90 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq43 eq11
  have eq95 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = (((X3 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq43 eq25
  have eq96 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ X4) = (((X3 ◇ (X3 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq43 eq26
  have eq99 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X3) ◇ X4)) = X3 := superpose eq43 eq32
  have eq111 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X4) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq43 eq95
  have eq112 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X3 ◇ X1) ◇ X4) := superpose eq43 eq96
  have eq113 (X1 X3 X4 : G) : ((X3 ◇ X1) ◇ X4) = X1 := superpose eq90 eq112
  have eq114 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq113 eq111
  have eq122 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq113 eq114
  have eq140 (X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X4) = X3 := superpose eq122 eq99
  have eq141 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X4) = X3 := superpose eq122 eq140
  have eq142 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq122 eq141
  have eq143 (X0 X3 : G) : X0 = X3 := superpose eq142 eq142
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq143 eq8
  subsumption eq162 eq143


@[equational_result]
theorem Equation22604_implies_Equation2 (G : Type*) [Magma G] (h : Equation22604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X2) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((X0 ◇ X0) ◇ X1) := superpose eq9 eq9
  have eq25 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ X3) = (((X0 ◇ X0) ◇ X1) ◇ X2) := superpose eq17 eq17
  have eq37 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ X3) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3))) ◇ X4)) := superpose eq17 eq9
  have eq50 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X3) = X0 := superpose eq7 eq25
  have eq97 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (X3 ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3))) ◇ X4)) := superpose eq50 eq37
  have eq99 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (X3 ◇ (X3 ◇ X4)) := superpose eq50 eq97
  have eq175 (X0 X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = X0 := superpose eq7 eq99
  have eq364 (X0 X3 : G) : X0 = X3 := superpose eq175 eq175
  have eq563 (X0 : G) : sK0 ≠ X0 := superpose eq364 eq8
  subsumption eq563 eq364


@[equational_result]
theorem Equation22606_implies_Equation2 (G : Type*) [Magma G] (h : Equation22606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ ((X1 ◇ X3) ◇ X1)) := superpose eq10 eq7
  have eq34 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0))) = X1 := superpose eq12 eq12
  have eq42 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq12 eq7
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X3) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))))) := superpose eq7 eq9
  have eq87 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X0 := superpose eq10 eq51
  have eq91 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq87 eq16
  have eq92 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ X1) := superpose eq87 eq18
  have eq95 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ X1) := superpose eq87 eq42
  have eq114 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) = X1 := superpose eq91 eq34
  have eq127 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq87 eq92
  have eq128 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X1 := superpose eq91 eq127
  have eq133 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := superpose eq87 eq95
  have eq134 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq91 eq133
  have eq136 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq134 eq114
  have eq143 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq91 eq136
  have eq144 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq143 eq91
  have eq149 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq144 eq128
  have eq161 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq144 eq149
  have eq163 (X0 X1 : G) : X0 = X1 := superpose eq144 eq161
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq163 eq8
  subsumption eq168 eq163


@[equational_result]
theorem Equation22608_implies_Equation2 (G : Type*) [Magma G] (h : Equation22608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X0 ◇ X5)) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X5 : G) : (X0 ◇ (X0 ◇ X5)) = X2 := superpose eq7 eq11
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq49 eq20


@[equational_result]
theorem Equation22610_implies_Equation2 (G : Type*) [Magma G] (h : Equation22610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((X4 ◇ (X4 ◇ (X0 ◇ X3))) ◇ (((X2 ◇ X0) ◇ X1) ◇ X4)) := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 : G) : ((((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq11
  have eq37 (X0 X1 X2 X3 : G) : (((((X2 ◇ X1) ◇ X0) ◇ (((X2 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ ((X3 ◇ X1) ◇ (((X2 ◇ X1) ◇ X0) ◇ (((X2 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))))) = X1 := superpose eq11 eq7
  have eq44 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X3) = (((X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (((X4 ◇ X1) ◇ X5) ◇ (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq10 eq12
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X2 ◇ X0) ◇ X3) ◇ X4) = (((X4 ◇ (X4 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (((X5 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X6) ◇ (X4 ◇ (X4 ◇ (X0 ◇ X1))))) := superpose eq12 eq12
  have eq59 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq11 eq12
  have eq103 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X4) = ((((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ ((X3 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X4))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq9 eq10
  have eq107 (X0 X1 X2 X4 X5 X6 : G) : ((X0 ◇ X1) ◇ X2) = ((X4 ◇ (X4 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (((X5 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X6) ◇ X4)) := superpose eq9 eq12
  have eq115 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq10 eq59
  have eq132 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ ((X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq59 eq9
  have eq133 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X0 ◇ (X4 ◇ X2)) ◇ ((X0 ◇ (X4 ◇ X2)) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)) := superpose eq59 eq12
  have eq135 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = (((X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq59 eq10
  have eq142 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X4) = (((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X4))) ◇ (X0 ◇ X1)) := superpose eq59 eq10
  have eq147 (X0 X1 X3 : G) : (X1 ◇ X3) = ((X0 ◇ X1) ◇ X3) := superpose eq115 eq135
  have eq148 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq147 eq9
  have eq156 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = ((((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (((X5 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq147 eq103
  have eq158 (X0 X1 X2 X4 X5 X6 : G) : ((X0 ◇ X1) ◇ X2) = ((X4 ◇ (X4 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (((X5 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X6) ◇ X4)) := superpose eq147 eq107
  have eq166 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq147 eq132
  have eq175 (X0 X1 X2 X3 X4 X6 : G) : (((X2 ◇ X0) ◇ X3) ◇ X4) = (((X4 ◇ (X4 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ ((((X2 ◇ X0) ◇ X3) ◇ X6) ◇ (X4 ◇ (X4 ◇ (X0 ◇ X1))))) := superpose eq147 eq45
  have eq187 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X3) = (((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (((X4 ◇ X1) ◇ X5) ◇ (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq147 eq44
  have eq191 (X0 X1 X2 : G) : (((((X2 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((((X2 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := superpose eq147 eq29
  have eq197 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = (((X4 ◇ X2) ◇ ((X0 ◇ (X4 ◇ X2)) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)) := superpose eq147 eq133
  have eq210 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ ((X3 ◇ X1) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))))) = X1 := superpose eq147 eq37
  have eq221 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (((X2 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq147 eq148
  have eq222 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq147 eq221
  have eq223 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq147 eq222
  have eq224 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq147 eq223
  have eq262 (X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = ((((X5 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (((X5 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq147 eq156
  have eq263 (X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X2 ◇ (X2 ◇ X1)) ◇ (((X5 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq147 eq262
  have eq264 (X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X2 ◇ X1) ◇ (((X5 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq147 eq263
  have eq265 (X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = ((X1 ◇ (((X5 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X1))) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq147 eq264
  have eq266 (X1 X2 X3 X4 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq147 eq265
  have eq267 (X1 X2 X3 X4 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = ((X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq147 eq266
  have eq268 (X1 X2 X3 X4 : G) : ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = ((X1 ◇ (X1 ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq147 eq267
  have eq269 (X1 X2 X4 : G) : (((X2 ◇ X1) ◇ X1) ◇ X4) = ((X1 ◇ (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq147 eq268
  have eq270 (X1 X2 X4 : G) : (X1 ◇ X4) = ((X1 ◇ (X1 ◇ (X1 ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq147 eq269
  have eq278 (X0 X1 X2 X4 X6 : G) : ((X0 ◇ X1) ◇ X2) = ((X4 ◇ (X4 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X6 ◇ X4)) := superpose eq147 eq158
  have eq279 (X1 X2 X4 X6 : G) : (X1 ◇ X2) = ((X4 ◇ (X4 ◇ (X1 ◇ X2))) ◇ (X6 ◇ X4)) := superpose eq147 eq278
  have eq303 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq147 eq166
  have eq304 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq147 eq303
  have eq305 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq147 eq304
  have eq329 (X0 X1 X2 X3 X4 X6 : G) : (((X2 ◇ X0) ◇ X3) ◇ X4) = (((X4 ◇ (X4 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X6 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X1))))) := superpose eq147 eq175
  have eq330 (X0 X1 X2 X3 X4 X6 : G) : (((X2 ◇ X0) ◇ X3) ◇ X4) = (((X4 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X6 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X1))))) := superpose eq147 eq329
  have eq331 (X0 X1 X2 X3 X4 X6 : G) : (((X2 ◇ X0) ◇ X3) ◇ X4) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X6 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X1))))) := superpose eq147 eq330
  have eq332 (X0 X1 X2 X3 X4 X6 : G) : (((X2 ◇ X0) ◇ X3) ◇ X4) = ((X1 ◇ (X0 ◇ X1)) ◇ (X6 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X1))))) := superpose eq147 eq331
  have eq333 (X0 X1 X3 X4 X6 : G) : ((X0 ◇ X3) ◇ X4) = ((X1 ◇ (X0 ◇ X1)) ◇ (X6 ◇ (X4 ◇ (X4 ◇ (X0 ◇ X1))))) := superpose eq147 eq332
  have eq388 (X0 X1 X2 X3 X5 : G) : (X1 ◇ X3) = (((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))))) := superpose eq147 eq187
  have eq389 (X1 X2 X3 X5 : G) : (X1 ◇ X3) = (((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2))))) := superpose eq147 eq388
  have eq390 (X1 X2 X3 X5 : G) : (X1 ◇ X3) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2))))) := superpose eq147 eq389
  have eq391 (X1 X2 X3 X5 : G) : (X1 ◇ X3) = ((X2 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X2))))) := superpose eq147 eq390
  have eq392 (X0 X3 X4 : G) : (X0 ◇ X4) = ((X0 ◇ X3) ◇ X4) := superpose eq391 eq333
  have eq410 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq147 eq191
  have eq411 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq147 eq410
  have eq412 (X0 X1 : G) : (((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq147 eq411
  have eq413 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq147 eq412
  have eq414 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq147 eq413
  have eq415 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq147 eq414
  have eq416 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq147 eq415
  have eq460 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ ((X0 ◇ (X4 ◇ X2)) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)) := superpose eq147 eq197
  have eq461 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ ((X4 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)) := superpose eq147 eq460
  have eq462 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)) := superpose eq147 eq461
  have eq489 (X0 X1 : G) : ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))))) = X1 := superpose eq147 eq210
  have eq490 (X0 X1 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))))) = X1 := superpose eq147 eq489
  have eq491 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := superpose eq147 eq490
  have eq492 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := superpose eq270 eq491
  have eq533 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X4) = ((X3 ◇ ((X0 ◇ X3) ◇ ((X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X4))) ◇ (X0 ◇ X1)) := superpose eq147 eq142
  have eq534 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X1)) = ((X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X4) := superpose eq392 eq533
  have eq538 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq224 eq224
  have eq553 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq534 eq538
  have eq554 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq462 eq553
  have eq556 (X1 X2 X4 X6 : G) : (X1 ◇ X2) = ((X4 ◇ (X1 ◇ X2)) ◇ (X6 ◇ X4)) := superpose eq554 eq279
  have eq570 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq554 eq305
  have eq578 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := superpose eq554 eq492
  have eq589 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq554 eq416
  have eq601 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq554 eq570
  have eq616 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq554 eq578
  have eq617 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq616 eq601
  have eq638 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq617 eq589
  have eq639 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq638 eq554
  have eq642 (X1 X4 X6 : G) : ((X4 ◇ X1) ◇ (X6 ◇ X4)) = X1 := superpose eq639 eq556
  have eq666 (X1 X4 X6 : G) : ((X4 ◇ X1) ◇ X6) = X1 := superpose eq639 eq642
  have eq667 (X1 X4 X6 : G) : (X4 ◇ X6) = X1 := superpose eq639 eq666
  have eq668 (X0 X3 : G) : X0 = X3 := superpose eq667 eq667
  have eq673 (X0 : G) : sK0 ≠ X0 := superpose eq668 eq8
  subsumption eq673 eq668


@[equational_result]
theorem Equation22612_implies_Equation2 (G : Type*) [Magma G] (h : Equation22612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X0) ◇ X3) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X4 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X0) ◇ X3) = ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) ◇ (X0 ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((X3 ◇ (X3 ◇ X0)) ◇ X0) ◇ X2) := superpose eq7 eq11
  have eq46 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X2) ◇ X4) = ((((X5 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2)) ◇ X2) ◇ X4) := superpose eq14 eq14
  have eq59 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ X1) ◇ X3)) ◇ ((X4 ◇ X3) ◇ X5)) = X3 := superpose eq14 eq7
  have eq116 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4) = ((((X5 ◇ (X5 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X6)) := superpose eq9 eq10
  have eq127 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4) = X2 := superpose eq59 eq116
  have eq138 (X2 X3 X4 : G) : (X2 ◇ X4) = ((X3 ◇ X2) ◇ X4) := superpose eq127 eq46
  have eq165 (X1 X2 X3 X4 : G) : ((X3 ◇ (X1 ◇ X2)) ◇ X4) = X2 := superpose eq138 eq127
  have eq222 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq165 eq165
  have eq239 (X0 X4 : G) : X0 = X4 := superpose eq165 eq222
  have eq288 (X0 : G) : sK0 ≠ X0 := superpose eq239 eq8
  subsumption eq288 eq239


@[equational_result]
theorem Equation22614_implies_Equation2 (G : Type*) [Magma G] (h : Equation22614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq10
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = (X0 ◇ ((X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0))) ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)))) := superpose eq10 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X2)) = (((((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X0) ◇ ((X4 ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0))) ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)))) := superpose eq10 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X2)) = (X0 ◇ ((X4 ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0))) ◇ (((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)))) := superpose eq14 eq19
  have eq21 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = (X3 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq17 eq20
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ (X4 ◇ X0)) = ((((X4 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X0) ◇ ((X5 ◇ ((X4 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))))) ◇ ((X4 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))))))) := superpose eq9 eq9
  have eq36 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq9
  have eq39 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))))) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = X0 := superpose eq9 eq7
  have eq50 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ (X4 ◇ X0)) = ((((X4 ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) ◇ ((X5 ◇ ((X4 ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))))) ◇ ((X4 ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))))) := superpose eq21 eq33
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ (X4 ◇ X0)) = ((((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X5 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq21 eq50
  have eq52 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ (X4 ◇ X0)) = ((((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq21 eq51
  have eq59 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = X0 := superpose eq21 eq39
  have eq60 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = X0 := superpose eq21 eq59
  have eq84 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) = X1 := superpose eq36 eq7
  have eq89 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) = ((((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ ((X4 ◇ ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq36 eq9
  have eq102 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X3 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) = X1 := superpose eq21 eq84
  have eq103 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq21 eq89
  have eq104 (X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) = X1 := superpose eq102 eq103
  have eq109 (X0 X1 X3 X4 : G) : ((X3 ◇ (X4 ◇ X0)) ◇ (X4 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq104 eq52
  have eq113 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X4 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) = X0 := superpose eq104 eq60
  have eq129 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq104 eq109
  have eq131 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq104 eq113
  have eq132 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq131 eq129
  have eq134 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = X0 := superpose eq132 eq7
  have eq143 (X0 X3 : G) : X0 = X3 := superpose eq134 eq134
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq143 eq8
  subsumption eq151 eq143


@[equational_result]
theorem Equation22616_implies_Equation2 (G : Type*) [Magma G] (h : Equation22616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X2) = X3 := superpose eq11 eq11
  have eq63 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq13 eq13
  have eq86 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq63
  have eq132 (X0 X4 : G) : X0 = X4 := superpose eq7 eq86
  have eq240 (X0 : G) : sK0 ≠ X0 := superpose eq132 eq8
  subsumption eq240 eq132


@[equational_result]
theorem Equation22620_implies_Equation2 (G : Type*) [Magma G] (h : Equation22620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X4)) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq10 eq10
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq48 eq26


@[equational_result]
theorem Equation22622_implies_Equation2 (G : Type*) [Magma G] (h : Equation22622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq115 eq42


@[equational_result]
theorem Equation22623_implies_Equation2 (G : Type*) [Magma G] (h : Equation22623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X2)) = X1 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq50 eq20


@[equational_result]
theorem Equation22624_implies_Equation2 (G : Type*) [Magma G] (h : Equation22624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq15
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq150 eq56


@[equational_result]
theorem Equation22625_implies_Equation2 (G : Type*) [Magma G] (h : Equation22625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X3 ◇ X4) ◇ X5)) = X2 := superpose eq7 eq7
  have eq20 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq50 eq20


@[equational_result]
theorem Equation22628_implies_Equation2 (G : Type*) [Magma G] (h : Equation22628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := superpose eq14 eq10
  have eq24 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq15
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq24 eq7
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq24 eq30
  have eq38 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq24 eq37
  have eq44 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq24 eq38
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq44 eq38
  have eq49 (X0 X1 : G) : X0 = X1 := superpose eq24 eq48
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq68 eq49


@[equational_result]
theorem Equation22631_implies_Equation2 (G : Type*) [Magma G] (h : Equation22631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq33 eq12


@[equational_result]
theorem Equation22633_implies_Equation2 (G : Type*) [Magma G] (h : Equation22633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X2)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq9
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq122 eq38


@[equational_result]
theorem Equation22635_implies_Equation2 (G : Type*) [Magma G] (h : Equation22635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq50 eq30


@[equational_result]
theorem Equation22638_implies_Equation2 (G : Type*) [Magma G] (h : Equation22638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = X1 := superpose eq11 eq9
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq11
  have eq23 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq14
  have eq24 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq23 eq13
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq24 eq24
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq51 eq37


@[equational_result]
theorem Equation22640_implies_Equation2 (G : Type*) [Magma G] (h : Equation22640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation22641_implies_Equation2 (G : Type*) [Magma G] (h : Equation22641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation22643_implies_Equation2 (G : Type*) [Magma G] (h : Equation22643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22644_implies_Equation2 (G : Type*) [Magma G] (h : Equation22644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22645_implies_Equation2 (G : Type*) [Magma G] (h : Equation22645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22647_implies_Equation2 (G : Type*) [Magma G] (h : Equation22647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) = ((((X4 ◇ X0) ◇ X2) ◇ (((X4 ◇ X0) ◇ X2) ◇ ((X4 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq7 eq9
  have eq27 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X1))) = X4 := superpose eq9 eq7
  have eq28 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X1))) = X4 := superpose eq9 eq7
  have eq33 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) := superpose eq10 eq19
  have eq40 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X1) ◇ X0) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X1))) = X4 := superpose eq22 eq27
  have eq41 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X1))) = X4 := superpose eq22 eq28
  have eq43 (X0 X2 : G) : (X2 ◇ X0) = (X2 ◇ X2) := superpose eq41 eq10
  have eq50 (X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq43 eq33
  have eq55 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq22 eq50
  have eq57 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq55 eq43
  have eq65 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X1))) = X4 := superpose eq57 eq40
  have eq74 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X4)) = X4 := superpose eq57 eq65
  have eq75 (X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ X3) = X4 := superpose eq57 eq74
  have eq76 (X2 X3 X4 : G) : (X2 ◇ X3) = X4 := superpose eq57 eq75
  have eq77 (X0 X3 : G) : X0 = X3 := superpose eq76 eq76
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq85 eq77


@[equational_result]
theorem Equation22649_implies_Equation2 (G : Type*) [Magma G] (h : Equation22649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq7 eq35
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq158 eq56


@[equational_result]
theorem Equation22651_implies_Equation2 (G : Type*) [Magma G] (h : Equation22651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22652_implies_Equation2 (G : Type*) [Magma G] (h : Equation22652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22653_implies_Equation2 (G : Type*) [Magma G] (h : Equation22653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22655_implies_Equation2 (G : Type*) [Magma G] (h : Equation22655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation22656_implies_Equation2 (G : Type*) [Magma G] (h : Equation22656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation22657_implies_Equation2 (G : Type*) [Magma G] (h : Equation22657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22659_implies_Equation2 (G : Type*) [Magma G] (h : Equation22659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22660_implies_Equation2 (G : Type*) [Magma G] (h : Equation22660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22661_implies_Equation2 (G : Type*) [Magma G] (h : Equation22661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22662_implies_Equation2 (G : Type*) [Magma G] (h : Equation22662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22664_implies_Equation2 (G : Type*) [Magma G] (h : Equation22664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X3) ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = X2 := superpose eq9 eq7
  have eq24 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq10 eq10
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ X0) := superpose eq9 eq10
  have eq38 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq24 eq25
  have eq39 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq38 eq17
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq38 eq39
  have eq53 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq38 eq52
  have eq54 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq38 eq53
  have eq57 (X0 X2 : G) : X0 = X2 := superpose eq54 eq54
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq59 eq57


@[equational_result]
theorem Equation22666_implies_Equation2 (G : Type*) [Magma G] (h : Equation22666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X4 ◇ X4) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) = ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X4)) := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : (X0 ◇ ((X4 ◇ X4) ◇ X5)) = X4 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X4)) = X0 := superpose eq14 eq10
  have eq31 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq21
  have eq42 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq31 eq14
  have eq59 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq31 eq42
  have eq63 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq59 eq42
  have eq66 (X0 X1 : G) : X0 = X1 := superpose eq31 eq63
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq85 eq66


@[equational_result]
theorem Equation22668_implies_Equation2 (G : Type*) [Magma G] (h : Equation22668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X3)) = ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) ◇ X0) := superpose eq9 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X4) = ((((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq9 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) ◇ X0) = ((X1 ◇ (X1 ◇ X2)) ◇ X4) := superpose eq11 eq18
  have eq21 (X1 X2 X4 : G) : (X1 ◇ (X1 ◇ X2)) = ((X1 ◇ (X1 ◇ X2)) ◇ X4) := superpose eq16 eq20
  have eq29 (X0 X1 X2 X4 X5 : G) : ((((X4 ◇ X1) ◇ X1) ◇ (((X4 ◇ X1) ◇ X1) ◇ X5)) ◇ (X4 ◇ ((X4 ◇ X1) ◇ X1))) = (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq10 eq10
  have eq33 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4)) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq7 eq10
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := superpose eq10 eq10
  have eq39 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ X3))) = X1 := superpose eq10 eq7
  have eq45 (X0 X1 X2 X4 X5 : G) : ((((X4 ◇ X1) ◇ X1) ◇ (((X4 ◇ X1) ◇ X1) ◇ X5)) ◇ (X4 ◇ ((X4 ◇ X1) ◇ X1))) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) := superpose eq21 eq29
  have eq48 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X4)) ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq21 eq33
  have eq59 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ X4)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (X1 ◇ X3))) = X1 := superpose eq21 eq39
  have eq60 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ X4)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = X1 := superpose eq21 eq59
  have eq83 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) = X0 := superpose eq37 eq7
  have eq89 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = ((((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X4)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)))) := superpose eq37 eq10
  have eq103 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq21 eq83
  have eq104 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X4)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq21 eq89
  have eq105 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq103 eq104
  have eq107 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq105 eq48
  have eq110 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = X1 := superpose eq105 eq60
  have eq112 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq105 eq10
  have eq114 (X0 X1 X4 X5 : G) : ((((X4 ◇ X1) ◇ X1) ◇ (((X4 ◇ X1) ◇ X1) ◇ X5)) ◇ (X4 ◇ ((X4 ◇ X1) ◇ X1))) = (X1 ◇ (X0 ◇ X1)) := superpose eq105 eq45
  have eq122 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq105 eq107
  have eq123 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) = X3 := superpose eq122 eq11
  have eq124 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X1) ◇ X1)) = X3 := superpose eq122 eq123
  have eq126 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq105 eq110
  have eq128 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = ((X0 ◇ X1) ◇ X0) := superpose eq124 eq112
  have eq132 (X1 X4 X5 : G) : ((((X4 ◇ X1) ◇ X1) ◇ (((X4 ◇ X1) ◇ X1) ◇ X5)) ◇ (X4 ◇ ((X4 ◇ X1) ◇ X1))) = X1 := superpose eq126 eq114
  have eq133 (X1 X4 X5 : G) : ((((X4 ◇ X1) ◇ X1) ◇ (((X4 ◇ X1) ◇ X1) ◇ X5)) ◇ X4) = X1 := superpose eq124 eq132
  have eq134 (X1 X4 : G) : ((X4 ◇ X1) ◇ X4) = X1 := superpose eq105 eq133
  have eq136 (X1 X3 : G) : (X1 ◇ (X1 ◇ X3)) = X1 := superpose eq134 eq128
  have eq138 (X1 X4 : G) : (X1 ◇ X4) = X1 := superpose eq136 eq21
  have eq146 (X1 X4 : G) : (X4 ◇ X4) = X1 := superpose eq138 eq134
  have eq181 (X0 X1 : G) : X0 = X1 := superpose eq138 eq146
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq181 eq8
  subsumption eq191 eq181


@[equational_result]
theorem Equation22669_implies_Equation2 (G : Type*) [Magma G] (h : Equation22669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X3) := superpose eq7 eq11
  have eq19 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ X3))) = ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq11 eq7
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2))) = X3 := superpose eq7 eq9
  have eq27 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)))) = X3 := superpose eq9 eq9
  have eq152 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq19 eq11
  have eq285 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq152 eq7
  have eq456 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq152 eq285
  have eq691 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)))) ◇ X0) := superpose eq456 eq12
  have eq692 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq456 eq21
  have eq711 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq691
  have eq712 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq692
  have eq846 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq712
  have eq884 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq846 eq711
  have eq900 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq846 eq884
  have eq901 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X3 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)))) = X3 := superpose eq900 eq27
  have eq1372 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1))) = X3 := superpose eq900 eq901
  have eq1373 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) = X3 := superpose eq900 eq1372
  have eq1374 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X1) = X3 := superpose eq900 eq1373
  have eq1375 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq900 eq1374
  have eq1376 (X0 X3 : G) : X0 = X3 := superpose eq1375 eq1375
  have eq1378 (X0 : G) : sK0 ≠ X0 := superpose eq1376 eq8
  subsumption eq1378 eq1376


@[equational_result]
theorem Equation22670_implies_Equation2 (G : Type*) [Magma G] (h : Equation22670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq46 eq17


@[equational_result]
theorem Equation22674_implies_Equation2 (G : Type*) [Magma G] (h : Equation22674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation22676_implies_Equation2 (G : Type*) [Magma G] (h : Equation22676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X5)))) = X2 := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq10 eq10
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq20 eq19
  have eq32 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq26 eq10
  have eq37 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X5))) = X2 := superpose eq32 eq14
  have eq45 (X1 X2 X5 : G) : (X1 ◇ (X1 ◇ X5)) = X2 := superpose eq32 eq37
  have eq46 (X1 X2 X5 : G) : (X1 ◇ X5) = X2 := superpose eq32 eq45
  have eq47 (X0 X3 : G) : X0 = X3 := superpose eq46 eq46
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq66 eq47


@[equational_result]
theorem Equation22677_implies_Equation2 (G : Type*) [Magma G] (h : Equation22677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X0) = X4 := superpose eq10 eq12
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq46 eq18


@[equational_result]
theorem Equation22678_implies_Equation2 (G : Type*) [Magma G] (h : Equation22678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X3)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) = X2 := superpose eq10 eq10
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq15
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq150 eq56


@[equational_result]
theorem Equation22679_implies_Equation2 (G : Type*) [Magma G] (h : Equation22679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation22681_implies_Equation2 (G : Type*) [Magma G] (h : Equation22681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq12 eq13
  have eq20 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq9
  have eq30 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ X4) ◇ X0)) = X4 := superpose eq9 eq9
  have eq43 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq10 eq30
  have eq44 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq30 eq30
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq44 eq43
  have eq60 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X3) ◇ X1)) = X3 := superpose eq56 eq20
  have eq79 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := superpose eq30 eq60
  have eq95 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq79 eq19
  have eq96 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq60 eq95
  have eq98 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = X0 := superpose eq96 eq7
  have eq122 (X0 X3 : G) : X0 = X3 := superpose eq98 eq98
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq8
  subsumption eq124 eq122


@[equational_result]
theorem Equation22683_implies_Equation2 (G : Type*) [Magma G] (h : Equation22683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = (X1 ◇ X3) := superpose eq7 eq7
  have eq20 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq7 eq12
  have eq79 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq163 eq79


@[equational_result]
theorem Equation22685_implies_Equation2 (G : Type*) [Magma G] (h : Equation22685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22686_implies_Equation2 (G : Type*) [Magma G] (h : Equation22686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22687_implies_Equation2 (G : Type*) [Magma G] (h : Equation22687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22689_implies_Equation2 (G : Type*) [Magma G] (h : Equation22689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation22690_implies_Equation2 (G : Type*) [Magma G] (h : Equation22690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation22691_implies_Equation2 (G : Type*) [Magma G] (h : Equation22691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22693_implies_Equation2 (G : Type*) [Magma G] (h : Equation22693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22694_implies_Equation2 (G : Type*) [Magma G] (h : Equation22694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22695_implies_Equation2 (G : Type*) [Magma G] (h : Equation22695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22696_implies_Equation2 (G : Type*) [Magma G] (h : Equation22696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22699_implies_Equation2 (G : Type*) [Magma G] (h : Equation22699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq10 eq7
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq12
  have eq31 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq10 eq12
  have eq39 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ ((X1 ◇ X3) ◇ X1)) = X3 := superpose eq12 eq7
  have eq44 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq16 eq16
  have eq53 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq44 eq7
  have eq55 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq44 eq10
  have eq61 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq44 eq16
  have eq65 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X1 ◇ X2))) = ((X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq44 eq20
  have eq74 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq44 eq31
  have eq81 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X3) ◇ X1)) = X3 := superpose eq44 eq39
  have eq101 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X1 ◇ (X3 ◇ X1))) = X3 := superpose eq44 eq81
  have eq102 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ (X3 ◇ X1))) = X3 := superpose eq44 eq101
  have eq116 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq53 eq61
  have eq117 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq61 eq61
  have eq121 (X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = X1 := superpose eq117 eq116
  have eq126 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((X3 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq121 eq65
  have eq145 (X0 X1 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ (X3 ◇ X1))) = X3 := superpose eq121 eq102
  have eq149 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq121 eq126
  have eq163 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq61 eq55
  have eq164 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq55 eq55
  have eq168 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq163 eq164
  have eq194 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq61 eq121
  have eq203 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq194 eq44
  have eq205 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq194 eq74
  have eq212 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ (X3 ◇ X1))) = X3 := superpose eq194 eq145
  have eq213 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X0 ◇ X2) ◇ (X2 ◇ X0)) := superpose eq194 eq149
  have eq224 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq203 eq205
  have eq238 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X1 ◇ X3)) = X3 := superpose eq194 eq212
  have eq239 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X3)) = X3 := superpose eq194 eq238
  have eq240 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X3)) = X3 := superpose eq194 eq239
  have eq241 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X3)) = X3 := superpose eq168 eq240
  have eq242 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq241 eq213
  have eq243 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq242 eq224
  have eq249 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X3 := superpose eq243 eq241
  have eq251 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq243 eq249
  have eq252 (X0 X1 : G) : X0 = X1 := superpose eq168 eq251
  have eq278 (X0 : G) : sK0 ≠ X0 := superpose eq252 eq8
  subsumption eq278 eq252


@[equational_result]
theorem Equation22700_implies_Equation2 (G : Type*) [Magma G] (h : Equation22700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = (X2 ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X4)) = X3 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq10 eq7
  have eq23 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq19 eq12
  have eq25 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X3 := superpose eq23 eq13
  have eq33 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq23 eq25
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq33 eq33
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq39 eq34


@[equational_result]
theorem Equation22702_implies_Equation2 (G : Type*) [Magma G] (h : Equation22702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22703_implies_Equation2 (G : Type*) [Magma G] (h : Equation22703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22704_implies_Equation2 (G : Type*) [Magma G] (h : Equation22704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22706_implies_Equation2 (G : Type*) [Magma G] (h : Equation22706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22707_implies_Equation2 (G : Type*) [Magma G] (h : Equation22707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22708_implies_Equation2 (G : Type*) [Magma G] (h : Equation22708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22710_implies_Equation2 (G : Type*) [Magma G] (h : Equation22710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22711_implies_Equation2 (G : Type*) [Magma G] (h : Equation22711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22712_implies_Equation2 (G : Type*) [Magma G] (h : Equation22712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22713_implies_Equation2 (G : Type*) [Magma G] (h : Equation22713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22715_implies_Equation2 (G : Type*) [Magma G] (h : Equation22715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq7 eq10
  have eq25 (X0 X1 X2 X4 : G) : (X2 ◇ X4) = ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq19 eq12
  have eq41 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq25 eq25
  have eq63 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X4) = X0 := superpose eq10 eq41
  have eq190 (X0 X4 : G) : X0 = X4 := superpose eq7 eq63
  have eq327 (X0 : G) : sK0 ≠ X0 := superpose eq190 eq8
  subsumption eq327 eq190


@[equational_result]
theorem Equation22716_implies_Equation2 (G : Type*) [Magma G] (h : Equation22716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X4 ◇ X5) ◇ ((X3 ◇ X0) ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X3) = ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq10 eq10
  have eq23 (X3 X4 : G) : (X4 ◇ X3) = X3 := superpose eq18 eq17
  have eq24 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ ((X3 ◇ X0) ◇ X2))) = X5 := superpose eq23 eq9
  have eq32 (X0 X2 X3 X5 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X2)) = X5 := superpose eq23 eq24
  have eq33 (X0 X2 X5 : G) : (X0 ◇ X2) = X5 := superpose eq23 eq32
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq33 eq33
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq36 eq34


@[equational_result]
theorem Equation22717_implies_Equation2 (G : Type*) [Magma G] (h : Equation22717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq10 eq10
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq152 eq47


@[equational_result]
theorem Equation22718_implies_Equation2 (G : Type*) [Magma G] (h : Equation22718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = (X3 ◇ X4) := superpose eq7 eq7
  have eq31 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq31
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq140 eq57


@[equational_result]
theorem Equation22720_implies_Equation2 (G : Type*) [Magma G] (h : Equation22720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22721_implies_Equation2 (G : Type*) [Magma G] (h : Equation22721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22722_implies_Equation2 (G : Type*) [Magma G] (h : Equation22722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22723_implies_Equation2 (G : Type*) [Magma G] (h : Equation22723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22725_implies_Equation2 (G : Type*) [Magma G] (h : Equation22725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22726_implies_Equation2 (G : Type*) [Magma G] (h : Equation22726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22727_implies_Equation2 (G : Type*) [Magma G] (h : Equation22727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22728_implies_Equation2 (G : Type*) [Magma G] (h : Equation22728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22730_implies_Equation2 (G : Type*) [Magma G] (h : Equation22730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22731_implies_Equation2 (G : Type*) [Magma G] (h : Equation22731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22732_implies_Equation2 (G : Type*) [Magma G] (h : Equation22732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22733_implies_Equation2 (G : Type*) [Magma G] (h : Equation22733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22735_implies_Equation2 (G : Type*) [Magma G] (h : Equation22735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22736_implies_Equation2 (G : Type*) [Magma G] (h : Equation22736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22737_implies_Equation2 (G : Type*) [Magma G] (h : Equation22737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22738_implies_Equation2 (G : Type*) [Magma G] (h : Equation22738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22739_implies_Equation2 (G : Type*) [Magma G] (h : Equation22739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22741_implies_Equation2 (G : Type*) [Magma G] (h : Equation22741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq10
  have eq39 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X1))) = X3 := superpose eq10 eq14
  have eq63 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq39 eq11
  have eq80 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2))) = ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) := superpose eq14 eq63
  have eq82 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq63 eq63
  have eq114 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq39 eq82
  have eq115 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq114 eq80
  have eq130 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq10 eq39
  have eq170 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq130 eq115
  have eq286 (X0 X3 : G) : X0 = X3 := superpose eq7 eq170
  have eq441 (X0 : G) : sK0 ≠ X0 := superpose eq286 eq8
  subsumption eq441 eq286


@[equational_result]
theorem Equation22742_implies_Equation2 (G : Type*) [Magma G] (h : Equation22742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X2 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ X2)) ◇ X0) = X2 := superpose eq10 eq7
  have eq22 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) := superpose eq22 eq11
  have eq131 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) := superpose eq12 eq11
  have eq145 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq131
  have eq146 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) := superpose eq145 eq33
  have eq149 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq146 eq15
  have eq207 (X0 X2 : G) : X0 = X2 := superpose eq10 eq149
  have eq327 (X0 : G) : sK0 ≠ X0 := superpose eq207 eq8
  subsumption eq327 eq207


@[equational_result]
theorem Equation22743_implies_Equation2 (G : Type*) [Magma G] (h : Equation22743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq125 eq38


@[equational_result]
theorem Equation22745_implies_Equation2 (G : Type*) [Magma G] (h : Equation22745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X1 ◇ X0) ◇ ((((X0 ◇ X2) ◇ X2) ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq12
  have eq16 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq12 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := superpose eq12 eq10
  have eq35 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ ((((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq14 eq10
  have eq37 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq14 eq35
  have eq46 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) := superpose eq14 eq9
  have eq52 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq14 eq9
  have eq54 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = ((((X0 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2)))))) := superpose eq10 eq9
  have eq64 (X0 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq14 eq16
  have eq86 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq46 eq64
  have eq87 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq86 eq52
  have eq88 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq86 eq87
  have eq92 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq88 eq14
  have eq93 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq88 eq37
  have eq96 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq92 eq12
  have eq108 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq92 eq96
  have eq115 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq92 eq93
  have eq119 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq115 eq108
  have eq126 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = (((X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X1) ◇ (X0 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))))) := superpose eq119 eq54
  have eq127 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq119 eq19
  have eq150 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ X2)) ◇ X1) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X2)))) = X2 := superpose eq119 eq126
  have eq151 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq127 eq115
  have eq153 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X2)))) = X2 := superpose eq151 eq150
  have eq156 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq151 eq119
  have eq161 (X0 X2 X3 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ X0) = X2 := superpose eq151 eq153
  have eq162 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq151 eq161
  have eq212 (X0 X1 : G) : X0 = X1 := superpose eq156 eq162
  have eq220 (X0 : G) : sK0 ≠ X0 := superpose eq212 eq8
  subsumption eq220 eq212


@[equational_result]
theorem Equation22747_implies_Equation2 (G : Type*) [Magma G] (h : Equation22747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq12 eq12
  have eq23 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = X3 := superpose eq14 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation22749_implies_Equation2 (G : Type*) [Magma G] (h : Equation22749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2)))))) = X1 := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq7 eq10
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq10
  have eq30 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq21 eq19
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X1))) = X1 := superpose eq30 eq16
  have eq36 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq35 eq10
  have eq48 (X0 X1 : G) : X0 = X1 := superpose eq7 eq36
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq61 eq48


@[equational_result]
theorem Equation22750_implies_Equation2 (G : Type*) [Magma G] (h : Equation22750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = ((X1 ◇ X0) ◇ ((((X0 ◇ X3) ◇ X3) ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X2 ◇ (X3 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X0)) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)))) = X2 := superpose eq10 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2) ◇ X2)) := superpose eq10 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = ((X2 ◇ X1) ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1))) ◇ (X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1)))) := superpose eq10 eq9
  have eq26 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ ((((((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) := superpose eq10 eq9
  have eq37 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = ((X2 ◇ X0) ◇ ((((((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose eq10 eq12
  have eq121 (X0 X1 : G) : ((X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose eq10 eq15
  have eq138 (X0 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq121 eq121
  have eq212 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = ((X1 ◇ (((((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq16 eq121
  have eq216 (X0 X1 : G) : ((X1 ◇ (((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) = X0 := superpose eq138 eq212
  have eq217 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) = X0 := superpose eq10 eq216
  have eq218 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq10 eq217
  have eq219 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq218 eq121
  have eq241 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) := superpose eq219 eq16
  have eq242 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq219 eq22
  have eq243 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X2 ◇ (X1 ◇ X0)) ◇ (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0))) := superpose eq219 eq26
  have eq244 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X2 ◇ X0) ◇ (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq219 eq37
  have eq350 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq219 eq241
  have eq352 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq219 eq242
  have eq353 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq350 eq352
  have eq354 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq219 eq243
  have eq355 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X0)) = X1 := superpose eq219 eq354
  have eq356 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X2 ◇ X0) ◇ X1) := superpose eq355 eq244
  have eq357 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq350 eq356
  have eq358 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq219 eq357
  have eq360 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ X0))) = X0 := superpose eq358 eq353
  have eq367 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X0 := superpose eq358 eq360
  have eq368 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq358 eq367
  have eq369 (X0 X3 : G) : X0 = X3 := superpose eq368 eq368
  have eq371 (X0 : G) : sK0 ≠ X0 := superpose eq369 eq8
  subsumption eq371 eq369


@[equational_result]
theorem Equation22751_implies_Equation2 (G : Type*) [Magma G] (h : Equation22751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X5)) = X2 := superpose eq10 eq10
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq12
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq47 eq25


@[equational_result]
theorem Equation22753_implies_Equation2 (G : Type*) [Magma G] (h : Equation22753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ X4) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq10
  have eq42 (X0 X1 X2 X5 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X5) ◇ X1)) = X2 := superpose eq12 eq7
  have eq62 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq19 eq10
  have eq84 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq42 eq62
  have eq127 (X0 X4 : G) : X0 = X4 := superpose eq7 eq84
  have eq250 (X0 : G) : sK0 ≠ X0 := superpose eq127 eq8
  subsumption eq250 eq127


@[equational_result]
theorem Equation22754_implies_Equation2 (G : Type*) [Magma G] (h : Equation22754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X4) ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq10 eq10
  have eq23 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X0) = X4 := superpose eq16 eq12
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation22755_implies_Equation2 (G : Type*) [Magma G] (h : Equation22755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq10 eq12
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq38 eq30


@[equational_result]
theorem Equation22756_implies_Equation2 (G : Type*) [Magma G] (h : Equation22756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X6)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq10 eq12
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq35 eq27


@[equational_result]
theorem Equation22758_implies_Equation2 (G : Type*) [Magma G] (h : Equation22758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (((X2 ◇ X0) ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq7 eq10
  have eq27 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq10 eq9
  have eq36 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose eq27 eq10
  have eq43 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq36 eq7
  have eq80 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq43 eq43
  have eq82 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq43 eq9
  have eq95 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq80
  have eq96 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq7 eq82
  have eq134 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq12 eq95
  have eq139 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq95 eq7
  have eq143 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq95 eq9
  have eq146 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq95 eq12
  have eq155 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq139 eq146
  have eq156 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq155 eq134
  have eq157 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq96 eq156
  have eq175 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq36 eq14
  have eq179 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq95 eq14
  have eq182 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq14 eq9
  have eq197 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) := superpose eq96 eq179
  have eq202 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) := superpose eq7 eq182
  have eq218 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq96
  have eq237 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq96 eq12
  have eq251 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) := superpose eq202 eq237
  have eq263 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq251 eq175
  have eq276 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq263 eq157
  have eq278 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq276 eq197
  have eq280 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq276 eq95
  have eq281 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) := superpose eq276 eq143
  have eq282 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq276 eq155
  have eq293 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq280 eq282
  have eq294 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq293 eq218
  have eq295 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose eq294 eq281
  have eq296 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ X0) := superpose eq293 eq295
  have eq297 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq280 eq296
  have eq298 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq297 eq9
  have eq349 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq297 eq298
  have eq350 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq349 eq278
  have eq357 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq350 eq36
  have eq381 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq350 eq357
  have eq389 (X0 X2 : G) : X0 = X2 := superpose eq381 eq381
  have eq391 (X0 : G) : sK0 ≠ X0 := superpose eq389 eq8
  subsumption eq391 eq389


@[equational_result]
theorem Equation22760_implies_Equation2 (G : Type*) [Magma G] (h : Equation22760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq20 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq10 eq10
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq138 eq44


@[equational_result]
theorem Equation22762_implies_Equation2 (G : Type*) [Magma G] (h : Equation22762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq7 eq9
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq122 eq38


@[equational_result]
theorem Equation22764_implies_Equation2 (G : Type*) [Magma G] (h : Equation22764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq11 eq11
  have eq21 (X0 X3 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X3 := superpose eq13 eq10
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq46 eq27


@[equational_result]
theorem Equation22767_implies_Equation2 (G : Type*) [Magma G] (h : Equation22767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ (X2 ◇ (X3 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (((X3 ◇ X0) ◇ (X3 ◇ X2)) ◇ (X3 ◇ X2))) = X2 := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 : G) : (((X3 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ (X3 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq10 eq7
  have eq55 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq11
  have eq59 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq11 eq9
  have eq82 (X0 X1 X2 : G) : (((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) ◇ (((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq10 eq55
  have eq111 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X3 ◇ X4)) ◇ ((X5 ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X4))) ◇ (X0 ◇ (X1 ◇ X4)))) ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X4))) ◇ (X0 ◇ (X1 ◇ X4))))) = (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X2 ◇ (X3 ◇ X4))) := superpose eq9 eq20
  have eq152 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2))) = X1 := superpose eq20 eq10
  have eq280 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq9 eq152
  have eq284 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) := superpose eq152 eq7
  have eq289 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1))) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq152 eq20
  have eq378 (X0 X1 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = ((((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := superpose eq13 eq9
  have eq437 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) = (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X0) ◇ X0)) := superpose eq7 eq284
  have eq456 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq152 eq284
  have eq507 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) = ((X2 ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)))) := superpose eq284 eq9
  have eq545 (X0 X1 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = ((((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq437 eq378
  have eq556 (X0 X1 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = ((((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq437 eq545
  have eq570 (X0 X1 : G) : (((X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose eq456 eq59
  have eq573 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) = ((X2 ◇ X2) ◇ (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ X1)) := superpose eq437 eq507
  have eq600 (X0 X1 : G) : (((((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X0) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq13 eq570
  have eq650 (X0 X1 : G) : (((((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) = (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose eq437 eq600
  have eq651 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = (((((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) := superpose eq437 eq650
  have eq663 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq7 eq456
  have eq712 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = ((X3 ◇ X2) ◇ ((X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0))) := superpose eq456 eq9
  have eq723 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) = X0 := superpose eq456 eq55
  have eq738 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq456 eq10
  have eq773 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X2)) = ((X3 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1))) := superpose eq663 eq289
  have eq776 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X2 ◇ (X3 ◇ X4))) = (X4 ◇ (((X0 ◇ (X1 ◇ X4)) ◇ X3) ◇ X3)) := superpose eq773 eq111
  have eq841 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq7 eq723
  have eq848 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq776 eq738
  have eq849 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq10 eq848
  have eq851 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq849 eq280
  have eq852 (X0 X1 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = (((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq849 eq556
  have eq859 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = ((((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ ((((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) := superpose eq849 eq651
  have eq864 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = ((X3 ◇ X2) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq849 eq712
  have eq886 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq849 eq456
  have eq942 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq849 eq851
  have eq948 (X0 X1 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = (((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq849 eq852
  have eq949 (X0 X1 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq849 eq948
  have eq950 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq942 eq949
  have eq951 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq849 eq950
  have eq952 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ X0) := superpose eq849 eq951
  have eq965 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = ((((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ (((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) := superpose eq849 eq859
  have eq966 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = (((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ (((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) := superpose eq849 eq965
  have eq975 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2)))) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) := superpose eq849 eq864
  have eq976 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) := superpose eq9 eq975
  have eq986 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X2) ◇ (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ X1)) := superpose eq976 eq573
  have eq1001 (X0 X1 X2 : G) : (((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq976 eq82
  have eq1012 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq976 eq986
  have eq1013 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := superpose eq1012 eq952
  have eq1020 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = (((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq1012 eq966
  have eq1021 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X0) := superpose eq284 eq1020
  have eq1032 (X0 X1 X2 : G) : (((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq849 eq1001
  have eq1033 (X0 X1 X2 : G) : (((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) = X2 := superpose eq849 eq1032
  have eq1079 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq849 eq886
  have eq1081 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := superpose eq1079 eq1013
  have eq1086 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq1079 eq1021
  have eq1605 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := superpose eq1079 eq1081
  have eq1611 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq849 eq1086
  have eq1612 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq1079 eq1611
  have eq1613 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq1079 eq1612
  have eq1614 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq1079 eq1613
  have eq1615 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq1614 eq1605
  have eq1616 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq1079 eq1615
  have eq1618 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq1616 eq841
  have eq1627 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1618 eq1079
  have eq1628 (X0 X1 X2 : G) : (((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) = X2 := superpose eq1627 eq1033
  have eq1639 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X2 := superpose eq1627 eq1628
  have eq1640 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) = X2 := superpose eq1627 eq1639
  have eq1641 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X2 := superpose eq1627 eq1640
  have eq1642 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq1627 eq1641
  have eq1643 (X0 X3 : G) : X0 = X3 := superpose eq1642 eq1642
  have eq1645 (X0 : G) : sK0 ≠ X0 := superpose eq1643 eq8
  subsumption eq1645 eq1643


@[equational_result]
theorem Equation22768_implies_Equation2 (G : Type*) [Magma G] (h : Equation22768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ (X0 ◇ X5)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ ((X2 ◇ X3) ◇ X4)) = X5 := superpose eq7 eq12
  have eq23 (X0 X4 X5 : G) : (X0 ◇ (X0 ◇ X5)) = X4 := superpose eq13 eq11
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq48 eq30


@[equational_result]
theorem Equation22770_implies_Equation2 (G : Type*) [Magma G] (h : Equation22770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X2 ◇ X4) ◇ X2) = ((X1 ◇ X0) ◇ ((X1 ◇ X5) ◇ X1)) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq7 eq9
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq130 eq58


@[equational_result]
theorem Equation22771_implies_Equation2 (G : Type*) [Magma G] (h : Equation22771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 X6 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X4) ◇ X5)) ◇ X6) = X5 := superpose eq7 eq12
  have eq15 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq12
  have eq24 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq15 eq13
  have eq76 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq153 eq76


@[equational_result]
theorem Equation22772_implies_Equation2 (G : Type*) [Magma G] (h : Equation22772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X4) ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X3 := superpose eq12 eq10
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq46 eq18


@[equational_result]
theorem Equation22773_implies_Equation2 (G : Type*) [Magma G] (h : Equation22773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X7 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ (X0 ◇ X7)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ (X0 ◇ X7)) = X4 := superpose eq12 eq11
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation22775_implies_Equation2 (G : Type*) [Magma G] (h : Equation22775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq7 eq10
  have eq42 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X2 ◇ X1)))) = X3 := superpose eq10 eq9
  have eq64 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq24 eq42
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq7 eq64
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq139 eq65


@[equational_result]
theorem Equation22776_implies_Equation2 (G : Type*) [Magma G] (h : Equation22776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) = (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))))) := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq10 eq10
  have eq32 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq10
  have eq34 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X3 ◇ X1))) = X3 := superpose eq10 eq9
  have eq46 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq7 eq29
  have eq47 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = X1 := superpose eq7 eq32
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq47 eq46
  have eq52 (X0 X1 X2 X4 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))))) = X2 := superpose eq47 eq19
  have eq55 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X1))) = X3 := superpose eq48 eq34
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq55 eq52
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq7 eq57
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq108 eq65


@[equational_result]
theorem Equation22777_implies_Equation2 (G : Type*) [Magma G] (h : Equation22777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq122 eq55


@[equational_result]
theorem Equation22781_implies_Equation2 (G : Type*) [Magma G] (h : Equation22781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq12 eq12
  have eq25 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = X3 := superpose eq14 eq10
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq25
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq52 eq32


@[equational_result]
theorem Equation22784_implies_Equation2 (G : Type*) [Magma G] (h : Equation22784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq33 eq12


@[equational_result]
theorem Equation22785_implies_Equation2 (G : Type*) [Magma G] (h : Equation22785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X4) = X5 := superpose eq12 eq12
  have eq23 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq14 eq10
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq47 eq25


@[equational_result]
theorem Equation22787_implies_Equation2 (G : Type*) [Magma G] (h : Equation22787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 X5 X6 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X6) = X5 := superpose eq12 eq12
  have eq25 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X4 := superpose eq16 eq11
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq25
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq61 eq37


@[equational_result]
theorem Equation22788_implies_Equation2 (G : Type*) [Magma G] (h : Equation22788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq62 eq19


@[equational_result]
theorem Equation22789_implies_Equation2 (G : Type*) [Magma G] (h : Equation22789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X3) ◇ X4) ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq64 eq17


@[equational_result]
theorem Equation22790_implies_Equation2 (G : Type*) [Magma G] (h : Equation22790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X7 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) ◇ (X0 ◇ X7)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X7 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X7)) = X4 := superpose eq12 eq11
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq51 eq31


@[equational_result]
theorem Equation22792_implies_Equation2 (G : Type*) [Magma G] (h : Equation22792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X4 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : (X3 ◇ X0) = (X1 ◇ X0) := superpose eq7 eq10
  have eq45 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X6 ◇ X2) ◇ (((X3 ◇ (X1 ◇ X2)) ◇ X4) ◇ (X5 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := superpose eq12 eq7
  have eq46 (X0 X1 X3 X4 : G) : (X4 ◇ ((X3 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq19
  have eq88 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X4) = X2 := superpose eq46 eq45
  have eq190 (X0 X3 : G) : X0 = X3 := superpose eq10 eq88
  have eq292 (X0 : G) : sK0 ≠ X0 := superpose eq190 eq8
  subsumption eq292 eq190


@[equational_result]
theorem Equation22793_implies_Equation2 (G : Type*) [Magma G] (h : Equation22793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ X2) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq10 eq10
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq10 eq17
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq124 eq68


@[equational_result]
theorem Equation22794_implies_Equation2 (G : Type*) [Magma G] (h : Equation22794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X4 ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq128 eq40


@[equational_result]
theorem Equation22795_implies_Equation2 (G : Type*) [Magma G] (h : Equation22795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ X4) ◇ X6)) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq40 (X0 X5 : G) : X0 = X5 := superpose eq7 eq18
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq128 eq40


@[equational_result]
theorem Equation22797_implies_Equation2 (G : Type*) [Magma G] (h : Equation22797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X4 X5 : G) : (((X0 ◇ X2) ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq12 eq12
  have eq18 (X0 X1 X2 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X2) = X4 := superpose eq12 eq12
  have eq19 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq12
  have eq20 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := superpose eq7 eq12
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq19 eq20
  have eq28 (X2 X5 : G) : (X5 ◇ X2) = X5 := superpose eq25 eq14
  have eq35 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X4 := superpose eq28 eq18
  have eq43 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X2) = X4 := superpose eq28 eq35
  have eq44 (X1 X2 X4 : G) : (X1 ◇ X2) = X4 := superpose eq28 eq43
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq44 eq44
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq64 eq53


@[equational_result]
theorem Equation22798_implies_Equation2 (G : Type*) [Magma G] (h : Equation22798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X3 ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) ◇ (X0 ◇ X4)) = X5 := superpose eq7 eq7
  have eq42 (X0 X6 : G) : X0 = X6 := superpose eq10 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq53 eq42


@[equational_result]
theorem Equation22799_implies_Equation2 (G : Type*) [Magma G] (h : Equation22799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X4)) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq69 eq22


@[equational_result]
theorem Equation22800_implies_Equation2 (G : Type*) [Magma G] (h : Equation22800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X6)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X2) = X5 := superpose eq12 eq12
  have eq23 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ X0)) = X4 := superpose eq14 eq10
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation22802_implies_Equation2 (G : Type*) [Magma G] (h : Equation22802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X3 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)) ◇ (X0 ◇ X1)) = X5 := superpose eq7 eq7
  have eq42 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq11 eq10
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq42
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq137 eq51


@[equational_result]
theorem Equation22803_implies_Equation2 (G : Type*) [Magma G] (h : Equation22803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X3 ◇ X2)) ◇ (X3 ◇ X2))) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq46 eq17


@[equational_result]
theorem Equation22804_implies_Equation2 (G : Type*) [Magma G] (h : Equation22804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X3 ◇ X2)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq43 eq19


@[equational_result]
theorem Equation22805_implies_Equation2 (G : Type*) [Magma G] (h : Equation22805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ (X3 ◇ X2)) ◇ X6)) = X4 := superpose eq7 eq7
  have eq22 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation22807_implies_Equation2 (G : Type*) [Magma G] (h : Equation22807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X4 := superpose eq11 eq11
  have eq23 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq18 eq12
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22808_implies_Equation2 (G : Type*) [Magma G] (h : Equation22808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ X4) ◇ (X3 ◇ X3))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation22809_implies_Equation2 (G : Type*) [Magma G] (h : Equation22809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X4 ◇ X4) ◇ X4)) = X3 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq52 eq20


@[equational_result]
theorem Equation22810_implies_Equation2 (G : Type*) [Magma G] (h : Equation22810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ X5) ◇ X6)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation22812_implies_Equation2 (G : Type*) [Magma G] (h : Equation22812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq33 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq11 eq10
  have eq42 (X0 X5 : G) : X0 = X5 := superpose eq7 eq33
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq115 eq42


@[equational_result]
theorem Equation22813_implies_Equation2 (G : Type*) [Magma G] (h : Equation22813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X3 ◇ X4))) = X2 := superpose eq7 eq7
  have eq22 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation22814_implies_Equation2 (G : Type*) [Magma G] (h : Equation22814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ X5)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation22815_implies_Equation2 (G : Type*) [Magma G] (h : Equation22815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ X6)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq50 eq19


@[equational_result]
theorem Equation22816_implies_Equation2 (G : Type*) [Magma G] (h : Equation22816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 X8 : G) : (X0 ◇ ((X6 ◇ X7) ◇ X8)) = X5 := superpose eq7 eq7
  have eq19 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation22820_implies_Equation2 (G : Type*) [Magma G] (h : Equation22820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq128 eq34


@[equational_result]
theorem Equation22822_implies_Equation2 (G : Type*) [Magma G] (h : Equation22822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ X1) ◇ X1)) = X3 := superpose eq11 eq7
  have eq20 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) ◇ (X3 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0))) = ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq11 eq9
  have eq57 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X4 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq7 eq10
  have eq59 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X3 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0)))) = ((((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))))) ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X4 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq10 eq10
  have eq66 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ (X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq7 eq10
  have eq94 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq11 eq66
  have eq95 (X0 X1 X2 X4 X5 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X0)) = ((((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))))) ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X4 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq94 eq59
  have eq96 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq94 eq57
  have eq119 (X0 X2 X4 X5 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X0)) = (((X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))) ◇ (X5 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))))) ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X4 ◇ ((X2 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq94 eq95
  have eq120 (X0 X2 X5 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X0)) = (((X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))) ◇ (X5 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))))) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq94 eq119
  have eq121 (X0 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X0)) = ((X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq94 eq120
  have eq122 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq94 eq96
  have eq123 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq94 eq122
  have eq124 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq123 eq121
  have eq127 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq94 eq124
  have eq128 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := superpose eq18 eq127
  have eq132 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X3 := superpose eq128 eq18
  have eq133 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X0))) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq128 eq20
  have eq139 (X0 X1 X3 : G) : (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq132 eq133
  have eq140 (X0 X1 X3 : G) : (X0 ◇ X1) = (X1 ◇ (X3 ◇ X1)) := superpose eq128 eq139
  have eq141 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq94 eq140
  have eq143 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq141 eq128
  have eq148 (X0 X1 : G) : X0 = X1 := superpose eq141 eq143
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq148 eq8
  subsumption eq153 eq148


@[equational_result]
theorem Equation22824_implies_Equation2 (G : Type*) [Magma G] (h : Equation22824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq49 eq37


@[equational_result]
theorem Equation22828_implies_Equation2 (G : Type*) [Magma G] (h : Equation22828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X5)) = X2 := superpose eq10 eq10
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq12
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq47 eq25


@[equational_result]
theorem Equation22830_implies_Equation2 (G : Type*) [Magma G] (h : Equation22830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X3)) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq10
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq130 eq58


@[equational_result]
theorem Equation22831_implies_Equation2 (G : Type*) [Magma G] (h : Equation22831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) ◇ X0) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq69 eq22


@[equational_result]
theorem Equation22832_implies_Equation2 (G : Type*) [Magma G] (h : Equation22832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X3 := superpose eq7 eq7
  have eq32 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq52 eq32


@[equational_result]
theorem Equation22833_implies_Equation2 (G : Type*) [Magma G] (h : Equation22833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X3 := superpose eq7 eq7
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation22835_implies_Equation2 (G : Type*) [Magma G] (h : Equation22835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ ((X1 ◇ X0) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) = (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2))) := superpose eq9 eq7
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X1) = X0 := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = ((((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ (X4 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0)))))) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq10 eq7
  have eq30 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq20 eq20
  have eq34 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0) = ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X0) := superpose eq20 eq9
  have eq39 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))) ◇ X1) = (((X1 ◇ (X2 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0) := superpose eq20 eq10
  have eq66 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq30 eq7
  have eq98 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0))))) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1)) = (((((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X4 ◇ (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))))) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1)) ◇ X0)) := superpose eq10 eq13
  have eq99 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)))) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) = (((((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X4 ◇ (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq13 eq13
  have eq125 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq20 eq66
  have eq149 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0))))) ◇ X1) = (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq125 eq98
  have eq151 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)))) ◇ X2) = (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X4 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq125 eq99
  have eq154 (X0 X1 X2 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0) = X1 := superpose eq125 eq39
  have eq165 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X0))) = ((((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ (X4 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0)))))) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq125 eq23
  have eq168 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq125 eq34
  have eq184 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0))))) ◇ X1) = (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) ◇ X0) := superpose eq125 eq149
  have eq185 (X0 X1 X2 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) ◇ X0) = X1 := superpose eq125 eq184
  have eq188 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)))) ◇ X2) = (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X4 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq125 eq151
  have eq189 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ X2) = (((X2 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq125 eq188
  have eq190 (X0 X1 X2 X4 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X0) = X2 := superpose eq125 eq189
  have eq199 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq154 eq165
  have eq202 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) = X1 := superpose eq199 eq154
  have eq203 (X0 X1 X2 X4 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ (X4 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X0) = X1 := superpose eq199 eq185
  have eq206 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X1 := superpose eq199 eq202
  have eq210 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq206 eq203
  have eq212 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq206 eq168
  have eq214 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq212 eq190
  have eq222 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq214 eq199
  have eq229 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq214 eq222
  have eq318 (X0 X1 : G) : X0 = X1 := superpose eq229 eq210
  have eq328 (X0 : G) : sK0 ≠ X0 := superpose eq318 eq8
  subsumption eq328 eq318


@[equational_result]
theorem Equation22837_implies_Equation2 (G : Type*) [Magma G] (h : Equation22837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq139 eq58


@[equational_result]
theorem Equation22839_implies_Equation2 (G : Type*) [Magma G] (h : Equation22839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22840_implies_Equation2 (G : Type*) [Magma G] (h : Equation22840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22841_implies_Equation2 (G : Type*) [Magma G] (h : Equation22841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22843_implies_Equation2 (G : Type*) [Magma G] (h : Equation22843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22844_implies_Equation2 (G : Type*) [Magma G] (h : Equation22844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22845_implies_Equation2 (G : Type*) [Magma G] (h : Equation22845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22847_implies_Equation2 (G : Type*) [Magma G] (h : Equation22847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22848_implies_Equation2 (G : Type*) [Magma G] (h : Equation22848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22849_implies_Equation2 (G : Type*) [Magma G] (h : Equation22849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22850_implies_Equation2 (G : Type*) [Magma G] (h : Equation22850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22854_implies_Equation2 (G : Type*) [Magma G] (h : Equation22854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq150 eq57


@[equational_result]
theorem Equation22856_implies_Equation2 (G : Type*) [Magma G] (h : Equation22856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation22857_implies_Equation2 (G : Type*) [Magma G] (h : Equation22857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation22858_implies_Equation2 (G : Type*) [Magma G] (h : Equation22858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22860_implies_Equation2 (G : Type*) [Magma G] (h : Equation22860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22861_implies_Equation2 (G : Type*) [Magma G] (h : Equation22861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22862_implies_Equation2 (G : Type*) [Magma G] (h : Equation22862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22864_implies_Equation2 (G : Type*) [Magma G] (h : Equation22864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22865_implies_Equation2 (G : Type*) [Magma G] (h : Equation22865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22866_implies_Equation2 (G : Type*) [Magma G] (h : Equation22866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22867_implies_Equation2 (G : Type*) [Magma G] (h : Equation22867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22869_implies_Equation2 (G : Type*) [Magma G] (h : Equation22869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : ((X5 ◇ X0) ◇ X3) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq7 eq10
  have eq80 (X0 X1 : G) : X0 = X1 := superpose eq7 eq25
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq168 eq80


@[equational_result]
theorem Equation22870_implies_Equation2 (G : Type*) [Magma G] (h : Equation22870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ X0) ◇ X4) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X3) = X0 := superpose eq7 eq10
  have eq92 (X0 X1 : G) : X0 = X1 := superpose eq7 eq25
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq172 eq92


@[equational_result]
theorem Equation22871_implies_Equation2 (G : Type*) [Magma G] (h : Equation22871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq10
  have eq22 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq16
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = X0 := superpose eq22 eq7
  have eq30 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X0 := superpose eq22 eq23
  have eq31 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq22 eq30
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation22872_implies_Equation2 (G : Type*) [Magma G] (h : Equation22872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq131 eq53


@[equational_result]
theorem Equation22874_implies_Equation2 (G : Type*) [Magma G] (h : Equation22874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22875_implies_Equation2 (G : Type*) [Magma G] (h : Equation22875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22876_implies_Equation2 (G : Type*) [Magma G] (h : Equation22876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22877_implies_Equation2 (G : Type*) [Magma G] (h : Equation22877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22879_implies_Equation2 (G : Type*) [Magma G] (h : Equation22879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22880_implies_Equation2 (G : Type*) [Magma G] (h : Equation22880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22881_implies_Equation2 (G : Type*) [Magma G] (h : Equation22881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22882_implies_Equation2 (G : Type*) [Magma G] (h : Equation22882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22884_implies_Equation2 (G : Type*) [Magma G] (h : Equation22884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22885_implies_Equation2 (G : Type*) [Magma G] (h : Equation22885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22886_implies_Equation2 (G : Type*) [Magma G] (h : Equation22886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22887_implies_Equation2 (G : Type*) [Magma G] (h : Equation22887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22889_implies_Equation2 (G : Type*) [Magma G] (h : Equation22889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22890_implies_Equation2 (G : Type*) [Magma G] (h : Equation22890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22891_implies_Equation2 (G : Type*) [Magma G] (h : Equation22891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22892_implies_Equation2 (G : Type*) [Magma G] (h : Equation22892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22893_implies_Equation2 (G : Type*) [Magma G] (h : Equation22893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22895_implies_Equation2 (G : Type*) [Magma G] (h : Equation22895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X1 ◇ X2))) = X3 := superpose eq9 eq9
  have eq23 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq14 eq10
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22896_implies_Equation2 (G : Type*) [Magma G] (h : Equation22896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) ◇ X0) = X2 := superpose eq9 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)))) ◇ X0) = X2 := superpose eq11 eq14
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq7 eq10
  have eq25 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ X2)) = X3 := superpose eq10 eq7
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X2 := superpose eq25 eq16
  have eq31 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq30 eq17
  have eq33 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ X0) := superpose eq31 eq10
  have eq39 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq33
  have eq81 (X0 X2 : G) : X0 = X2 := superpose eq39 eq39
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq83 eq81


@[equational_result]
theorem Equation22897_implies_Equation2 (G : Type*) [Magma G] (h : Equation22897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation22901_implies_Equation2 (G : Type*) [Magma G] (h : Equation22901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation22904_implies_Equation2 (G : Type*) [Magma G] (h : Equation22904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X2)) = ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq9 eq9
  have eq25 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq17 eq17
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X3 ◇ (((X4 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X4 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) ◇ (X4 ◇ ((X4 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) := superpose eq17 eq9
  have eq50 (X0 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq25
  have eq98 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X3 ◇ X4) ◇ (X4 ◇ ((X4 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) := superpose eq50 eq33
  have eq100 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X3 ◇ X4) ◇ X4) := superpose eq50 eq98
  have eq175 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X4) = X0 := superpose eq7 eq100
  have eq364 (X0 X3 : G) : X0 = X3 := superpose eq175 eq175
  have eq563 (X0 : G) : sK0 ≠ X0 := superpose eq364 eq8
  subsumption eq563 eq364


@[equational_result]
theorem Equation22905_implies_Equation2 (G : Type*) [Magma G] (h : Equation22905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X5)) = X2 := superpose eq10 eq10
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq12
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq47 eq25


@[equational_result]
theorem Equation22907_implies_Equation2 (G : Type*) [Magma G] (h : Equation22907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X1 ◇ X2))) = X4 := superpose eq9 eq9
  have eq23 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq14 eq10
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22908_implies_Equation2 (G : Type*) [Magma G] (h : Equation22908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ X2) ◇ X3))) ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq9 eq9
  have eq21 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X0) = X4 := superpose eq15 eq11
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq46 eq27


@[equational_result]
theorem Equation22909_implies_Equation2 (G : Type*) [Magma G] (h : Equation22909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ X4) ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq9 eq9
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq138 eq60


@[equational_result]
theorem Equation22910_implies_Equation2 (G : Type*) [Magma G] (h : Equation22910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation22913_implies_Equation2 (G : Type*) [Magma G] (h : Equation22913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X2) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X3) ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ X4)) ◇ (X3 ◇ X4)) := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) := superpose eq10 eq10
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) ◇ X2) = X0 := superpose eq7 eq10
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq10 eq9
  have eq33 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X4)) := superpose eq10 eq7
  have eq36 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq22 eq9
  have eq52 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X0))) ◇ X4) = (((X1 ◇ (X4 ◇ X4)) ◇ (X3 ◇ X3)) ◇ X0) := superpose eq26 eq10
  have eq62 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq7 eq11
  have eq94 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) = X1 := superpose eq27 eq26
  have eq98 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X0)) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq27 eq7
  have eq116 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq7 eq98
  have eq137 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = (((X1 ◇ (X3 ◇ X3)) ◇ ((((X4 ◇ (X4 ◇ X2)) ◇ (X4 ◇ X2)) ◇ (X0 ◇ (X4 ◇ X2))) ◇ (((X4 ◇ (X4 ◇ X2)) ◇ (X4 ◇ X2)) ◇ (X0 ◇ (X4 ◇ X2))))) ◇ X0) := superpose eq36 eq10
  have eq143 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = (((X1 ◇ (X3 ◇ X3)) ◇ (((X4 ◇ (X4 ◇ X2)) ◇ ((X4 ◇ X2) ◇ (X4 ◇ X2))) ◇ ((X0 ◇ (X4 ◇ X2)) ◇ (X0 ◇ (X4 ◇ X2))))) ◇ X0) := superpose eq62 eq137
  have eq145 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq116 eq116
  have eq167 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq145 eq94
  have eq171 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ X4)) ◇ (X3 ◇ X4)) = (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X1) := superpose eq167 eq20
  have eq172 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = (((X0 ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X4)) := superpose eq167 eq33
  have eq176 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X0))) ◇ X4) = ((X1 ◇ (X4 ◇ X4)) ◇ X0) := superpose eq167 eq52
  have eq185 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = (((X1 ◇ (X3 ◇ X3)) ◇ ((X4 ◇ (X4 ◇ X2)) ◇ ((X0 ◇ (X4 ◇ X2)) ◇ (X0 ◇ (X4 ◇ X2))))) ◇ X0) := superpose eq167 eq143
  have eq228 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X4 ◇ X4)) ◇ (X3 ◇ X4)) := superpose eq167 eq171
  have eq229 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) := superpose eq167 eq228
  have eq231 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) = X2 := superpose eq229 eq36
  have eq238 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((X0 ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X4)) := superpose eq167 eq172
  have eq239 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X4)) := superpose eq167 eq238
  have eq246 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X0))) ◇ X4) := superpose eq167 eq176
  have eq247 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X4) := superpose eq167 eq246
  have eq261 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = (((X1 ◇ (X3 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X2))) ◇ X0) := superpose eq167 eq185
  have eq262 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X1 ◇ (X4 ◇ (X4 ◇ X2))) ◇ X0) := superpose eq167 eq261
  have eq263 (X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X3) := superpose eq247 eq262
  have eq273 (X0 X1 X3 X4 : G) : (X1 ◇ X3) = (X0 ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq263 eq239
  have eq281 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq263 eq231
  have eq294 (X0 X1 X3 : G) : (X1 ◇ X3) = (X0 ◇ (X0 ◇ X1)) := superpose eq263 eq273
  have eq296 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq281 eq294
  have eq300 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq296 eq281
  have eq305 (X0 X3 : G) : X0 = X3 := superpose eq300 eq300
  have eq307 (X0 : G) : sK0 ≠ X0 := superpose eq305 eq8
  subsumption eq307 eq305


@[equational_result]
theorem Equation22914_implies_Equation2 (G : Type*) [Magma G] (h : Equation22914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ (X2 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq60 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq183 eq60


@[equational_result]
theorem Equation22916_implies_Equation2 (G : Type*) [Magma G] (h : Equation22916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation22917_implies_Equation2 (G : Type*) [Magma G] (h : Equation22917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22918_implies_Equation2 (G : Type*) [Magma G] (h : Equation22918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22920_implies_Equation2 (G : Type*) [Magma G] (h : Equation22920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22921_implies_Equation2 (G : Type*) [Magma G] (h : Equation22921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22922_implies_Equation2 (G : Type*) [Magma G] (h : Equation22922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22924_implies_Equation2 (G : Type*) [Magma G] (h : Equation22924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22925_implies_Equation2 (G : Type*) [Magma G] (h : Equation22925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22926_implies_Equation2 (G : Type*) [Magma G] (h : Equation22926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22927_implies_Equation2 (G : Type*) [Magma G] (h : Equation22927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22930_implies_Equation2 (G : Type*) [Magma G] (h : Equation22930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ X3) := superpose eq10 eq10
  have eq40 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq15
  have eq102 (X0 X2 : G) : X0 = X2 := superpose eq40 eq40
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq182 eq102


@[equational_result]
theorem Equation22931_implies_Equation2 (G : Type*) [Magma G] (h : Equation22931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq141 eq54


@[equational_result]
theorem Equation22933_implies_Equation2 (G : Type*) [Magma G] (h : Equation22933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22934_implies_Equation2 (G : Type*) [Magma G] (h : Equation22934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22935_implies_Equation2 (G : Type*) [Magma G] (h : Equation22935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22937_implies_Equation2 (G : Type*) [Magma G] (h : Equation22937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22938_implies_Equation2 (G : Type*) [Magma G] (h : Equation22938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation22939_implies_Equation2 (G : Type*) [Magma G] (h : Equation22939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22941_implies_Equation2 (G : Type*) [Magma G] (h : Equation22941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22942_implies_Equation2 (G : Type*) [Magma G] (h : Equation22942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22943_implies_Equation2 (G : Type*) [Magma G] (h : Equation22943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22944_implies_Equation2 (G : Type*) [Magma G] (h : Equation22944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22946_implies_Equation2 (G : Type*) [Magma G] (h : Equation22946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X1 ◇ X2))) = X5 := superpose eq9 eq9
  have eq23 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq14 eq10
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation22947_implies_Equation2 (G : Type*) [Magma G] (h : Equation22947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X0))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ X0) ◇ X4) = ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9
  have eq44 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1))) = X2 := superpose eq10 eq9
  have eq66 (X1 X2 X3 : G) : (X3 ◇ X1) = X2 := superpose eq17 eq44
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq66
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq141 eq67


@[equational_result]
theorem Equation22948_implies_Equation2 (G : Type*) [Magma G] (h : Equation22948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X4 ◇ X4) = ((X1 ◇ (X2 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq7 eq31
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq161 eq51


@[equational_result]
theorem Equation22949_implies_Equation2 (G : Type*) [Magma G] (h : Equation22949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation22951_implies_Equation2 (G : Type*) [Magma G] (h : Equation22951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22952_implies_Equation2 (G : Type*) [Magma G] (h : Equation22952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22953_implies_Equation2 (G : Type*) [Magma G] (h : Equation22953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22954_implies_Equation2 (G : Type*) [Magma G] (h : Equation22954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22956_implies_Equation2 (G : Type*) [Magma G] (h : Equation22956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22957_implies_Equation2 (G : Type*) [Magma G] (h : Equation22957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation22958_implies_Equation2 (G : Type*) [Magma G] (h : Equation22958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22959_implies_Equation2 (G : Type*) [Magma G] (h : Equation22959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22961_implies_Equation2 (G : Type*) [Magma G] (h : Equation22961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22962_implies_Equation2 (G : Type*) [Magma G] (h : Equation22962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22963_implies_Equation2 (G : Type*) [Magma G] (h : Equation22963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22964_implies_Equation2 (G : Type*) [Magma G] (h : Equation22964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22966_implies_Equation2 (G : Type*) [Magma G] (h : Equation22966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22967_implies_Equation2 (G : Type*) [Magma G] (h : Equation22967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22968_implies_Equation2 (G : Type*) [Magma G] (h : Equation22968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation22969_implies_Equation2 (G : Type*) [Magma G] (h : Equation22969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation22970_implies_Equation2 (G : Type*) [Magma G] (h : Equation22970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation22972_implies_Equation2 (G : Type*) [Magma G] (h : Equation22972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ X4) ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq34
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq140 eq42


@[equational_result]
theorem Equation22973_implies_Equation2 (G : Type*) [Magma G] (h : Equation22973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X5 ◇ X5) ◇ (X2 ◇ (X3 ◇ X4)))) = X5 := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq9 eq9
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq30
  have eq144 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq144 eq44


@[equational_result]
theorem Equation22974_implies_Equation2 (G : Type*) [Magma G] (h : Equation22974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X4 ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X0) = X5 := superpose eq10 eq9
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq43 eq17


@[equational_result]
theorem Equation22975_implies_Equation2 (G : Type*) [Magma G] (h : Equation22975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ ((X5 ◇ X5) ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation22977_implies_Equation2 (G : Type*) [Magma G] (h : Equation22977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ ((X5 ◇ X1) ◇ X1)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X1 := superpose eq7 eq7
  have eq33 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq9 eq12
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq115 eq42


@[equational_result]
theorem Equation22978_implies_Equation2 (G : Type*) [Magma G] (h : Equation22978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X5 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4)))) = X5 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq9 eq9
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq119 eq45


@[equational_result]
theorem Equation22979_implies_Equation2 (G : Type*) [Magma G] (h : Equation22979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X6 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ ((X0 ◇ X4) ◇ X6))) = X2 := superpose eq7 eq10
  have eq15 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X5)) = X2 := superpose eq7 eq10
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq13
  have eq76 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq153 eq76


@[equational_result]
theorem Equation22980_implies_Equation2 (G : Type*) [Magma G] (h : Equation22980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X5 := superpose eq7 eq7
  have eq35 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation22982_implies_Equation2 (G : Type*) [Magma G] (h : Equation22982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq41 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq137 eq51


@[equational_result]
theorem Equation22983_implies_Equation2 (G : Type*) [Magma G] (h : Equation22983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ ((X4 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq10 eq10
  have eq63 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)))) = X2 := superpose eq10 eq15
  have eq86 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq63
  have eq132 (X0 X4 : G) : X0 = X4 := superpose eq7 eq86
  have eq240 (X0 : G) : sK0 ≠ X0 := superpose eq132 eq8
  subsumption eq240 eq132


@[equational_result]
theorem Equation22984_implies_Equation2 (G : Type*) [Magma G] (h : Equation22984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X5 ◇ (X2 ◇ (X3 ◇ X4))) ◇ ((X0 ◇ X3) ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ (X0 ◇ X2)) ◇ X3)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X0) ◇ X5)) = X4 := superpose eq7 eq10
  have eq23 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X0) = X5 := superpose eq13 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq48 eq30


@[equational_result]
theorem Equation22985_implies_Equation2 (G : Type*) [Magma G] (h : Equation22985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ (X0 ◇ X2)) ◇ X6)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X5)) = X2 := superpose eq10 eq10
  have eq23 (X0 X2 X5 : G) : (X2 ◇ X0) = X5 := superpose eq14 eq12
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq47 eq25


@[equational_result]
theorem Equation22987_implies_Equation2 (G : Type*) [Magma G] (h : Equation22987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq133 eq48


@[equational_result]
theorem Equation22988_implies_Equation2 (G : Type*) [Magma G] (h : Equation22988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X4 ◇ X2) ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X3 ◇ X2))) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq10 eq10
  have eq25 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X0) = X4 := superpose eq16 eq12
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq25
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq52 eq32


@[equational_result]
theorem Equation22989_implies_Equation2 (G : Type*) [Magma G] (h : Equation22989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X5 ◇ ((X0 ◇ X4) ◇ X4)) ◇ ((X0 ◇ X4) ◇ X4))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X0) = X5 := superpose eq7 eq9
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq49 eq20


@[equational_result]
theorem Equation22990_implies_Equation2 (G : Type*) [Magma G] (h : Equation22990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 X6 X7 : G) : ((X1 ◇ X0) ◇ ((X6 ◇ ((X0 ◇ X4) ◇ X5)) ◇ X7)) = X6 := superpose eq7 eq7
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ X4) ◇ X6)) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X6 X7 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X7)) = X6 := superpose eq10 eq9
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq51 eq31


@[equational_result]
theorem Equation22992_implies_Equation2 (G : Type*) [Magma G] (h : Equation22992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X1 ◇ (X2 ◇ X3)))) = X5 := superpose eq7 eq7
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq42 (X0 X5 : G) : X0 = X5 := superpose eq7 eq34
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq115 eq42


@[equational_result]
theorem Equation22993_implies_Equation2 (G : Type*) [Magma G] (h : Equation22993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X0 ◇ X4))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq10 eq10
  have eq23 (X0 X2 X5 : G) : ((X0 ◇ X2) ◇ X0) = X5 := superpose eq16 eq12
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation22994_implies_Equation2 (G : Type*) [Magma G] (h : Equation22994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 X6 X7 : G) : ((X1 ◇ X0) ◇ ((X6 ◇ X7) ◇ ((X0 ◇ X5) ◇ X4))) = X6 := superpose eq7 eq7
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ X3)) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X6 : G) : ((X1 ◇ X0) ◇ X0) = X6 := superpose eq10 eq9
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation22995_implies_Equation2 (G : Type*) [Magma G] (h : Equation22995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X4 := superpose eq7 eq7
  have eq32 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq52 eq32


@[equational_result]
theorem Equation22996_implies_Equation2 (G : Type*) [Magma G] (h : Equation22996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X4 := superpose eq7 eq7
  have eq29 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation22998_implies_Equation2 (G : Type*) [Magma G] (h : Equation22998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq28 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq10 eq10
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq28
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq116 eq36


@[equational_result]
theorem Equation22999_implies_Equation2 (G : Type*) [Magma G] (h : Equation22999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X5) ◇ (X2 ◇ (X3 ◇ X4)))) = X5 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq9 eq9
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq166 eq54


@[equational_result]
theorem Equation23000_implies_Equation2 (G : Type*) [Magma G] (h : Equation23000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X5) ◇ ((X2 ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X4 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X4)) = X5 := superpose eq7 eq10
  have eq24 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X0) = X5 := superpose eq15 eq9
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq24
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq55 eq31


@[equational_result]
theorem Equation23001_implies_Equation2 (G : Type*) [Magma G] (h : Equation23001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X5) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq35
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq133 eq57


@[equational_result]
theorem Equation23003_implies_Equation2 (G : Type*) [Magma G] (h : Equation23003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23004_implies_Equation2 (G : Type*) [Magma G] (h : Equation23004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23005_implies_Equation2 (G : Type*) [Magma G] (h : Equation23005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23006_implies_Equation2 (G : Type*) [Magma G] (h : Equation23006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23008_implies_Equation2 (G : Type*) [Magma G] (h : Equation23008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23009_implies_Equation2 (G : Type*) [Magma G] (h : Equation23009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23010_implies_Equation2 (G : Type*) [Magma G] (h : Equation23010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23011_implies_Equation2 (G : Type*) [Magma G] (h : Equation23011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23013_implies_Equation2 (G : Type*) [Magma G] (h : Equation23013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23014_implies_Equation2 (G : Type*) [Magma G] (h : Equation23014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23015_implies_Equation2 (G : Type*) [Magma G] (h : Equation23015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23016_implies_Equation2 (G : Type*) [Magma G] (h : Equation23016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23018_implies_Equation2 (G : Type*) [Magma G] (h : Equation23018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23019_implies_Equation2 (G : Type*) [Magma G] (h : Equation23019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23020_implies_Equation2 (G : Type*) [Magma G] (h : Equation23020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23021_implies_Equation2 (G : Type*) [Magma G] (h : Equation23021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23022_implies_Equation2 (G : Type*) [Magma G] (h : Equation23022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23024_implies_Equation2 (G : Type*) [Magma G] (h : Equation23024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X5) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X4) ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq40 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq10
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq40
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq160 eq51


@[equational_result]
theorem Equation23025_implies_Equation2 (G : Type*) [Magma G] (h : Equation23025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X4) ◇ (X2 ◇ X0))) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ X0) := superpose eq7 eq10
  have eq41 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq10 eq17
  have eq141 (X0 X4 : G) : X0 = X4 := superpose eq7 eq41
  have eq271 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq271 eq141


@[equational_result]
theorem Equation23026_implies_Equation2 (G : Type*) [Magma G] (h : Equation23026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X5) ◇ ((X3 ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ X4)) := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X0)) ◇ X5)) = X5 := superpose eq15 eq9
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X5)) = X5 := superpose eq15 eq23
  have eq25 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ X3) ◇ X5)) = X5 := superpose eq15 eq24
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq7 eq25
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq47 eq36


@[equational_result]
theorem Equation23027_implies_Equation2 (G : Type*) [Magma G] (h : Equation23027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ (((X2 ◇ X0) ◇ X5) ◇ X6)) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq18
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq140 eq57


@[equational_result]
theorem Equation23029_implies_Equation2 (G : Type*) [Magma G] (h : Equation23029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23030_implies_Equation2 (G : Type*) [Magma G] (h : Equation23030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23031_implies_Equation2 (G : Type*) [Magma G] (h : Equation23031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23032_implies_Equation2 (G : Type*) [Magma G] (h : Equation23032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23034_implies_Equation2 (G : Type*) [Magma G] (h : Equation23034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23035_implies_Equation2 (G : Type*) [Magma G] (h : Equation23035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23036_implies_Equation2 (G : Type*) [Magma G] (h : Equation23036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23037_implies_Equation2 (G : Type*) [Magma G] (h : Equation23037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23039_implies_Equation2 (G : Type*) [Magma G] (h : Equation23039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23040_implies_Equation2 (G : Type*) [Magma G] (h : Equation23040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23041_implies_Equation2 (G : Type*) [Magma G] (h : Equation23041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23042_implies_Equation2 (G : Type*) [Magma G] (h : Equation23042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23044_implies_Equation2 (G : Type*) [Magma G] (h : Equation23044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23045_implies_Equation2 (G : Type*) [Magma G] (h : Equation23045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23046_implies_Equation2 (G : Type*) [Magma G] (h : Equation23046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23047_implies_Equation2 (G : Type*) [Magma G] (h : Equation23047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23048_implies_Equation2 (G : Type*) [Magma G] (h : Equation23048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23050_implies_Equation2 (G : Type*) [Magma G] (h : Equation23050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X4) ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq20 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq157 eq49


@[equational_result]
theorem Equation23051_implies_Equation2 (G : Type*) [Magma G] (h : Equation23051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X4) ◇ (X3 ◇ X0))) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X3)) = ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2)) := superpose eq10 eq7
  have eq23 (X0 X3 X4 X5 : G) : ((X4 ◇ X0) ◇ (X5 ◇ X3)) = X3 := superpose eq18 eq20
  have eq24 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq23 eq10
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq24 eq24
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq38 eq27


@[equational_result]
theorem Equation23052_implies_Equation2 (G : Type*) [Magma G] (h : Equation23052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ ((((X4 ◇ X0) ◇ X4) ◇ X5) ◇ ((X4 ◇ X0) ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ X3)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X0) = X5 := superpose eq10 eq9
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation23053_implies_Equation2 (G : Type*) [Magma G] (h : Equation23053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq133 eq53


@[equational_result]
theorem Equation23055_implies_Equation2 (G : Type*) [Magma G] (h : Equation23055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23056_implies_Equation2 (G : Type*) [Magma G] (h : Equation23056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23057_implies_Equation2 (G : Type*) [Magma G] (h : Equation23057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23058_implies_Equation2 (G : Type*) [Magma G] (h : Equation23058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23060_implies_Equation2 (G : Type*) [Magma G] (h : Equation23060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23061_implies_Equation2 (G : Type*) [Magma G] (h : Equation23061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23062_implies_Equation2 (G : Type*) [Magma G] (h : Equation23062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23063_implies_Equation2 (G : Type*) [Magma G] (h : Equation23063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23065_implies_Equation2 (G : Type*) [Magma G] (h : Equation23065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23066_implies_Equation2 (G : Type*) [Magma G] (h : Equation23066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23067_implies_Equation2 (G : Type*) [Magma G] (h : Equation23067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23068_implies_Equation2 (G : Type*) [Magma G] (h : Equation23068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23070_implies_Equation2 (G : Type*) [Magma G] (h : Equation23070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23071_implies_Equation2 (G : Type*) [Magma G] (h : Equation23071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23072_implies_Equation2 (G : Type*) [Magma G] (h : Equation23072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23073_implies_Equation2 (G : Type*) [Magma G] (h : Equation23073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23074_implies_Equation2 (G : Type*) [Magma G] (h : Equation23074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23076_implies_Equation2 (G : Type*) [Magma G] (h : Equation23076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X6 X7 : G) : ((X1 ◇ X0) ◇ ((X6 ◇ X7) ◇ X1)) = X7 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X1 ◇ (X2 ◇ X3)))) = X6 := superpose eq7 eq7
  have eq33 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq9 eq10
  have eq42 (X0 X5 : G) : X0 = X5 := superpose eq7 eq33
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq147 eq42


@[equational_result]
theorem Equation23077_implies_Equation2 (G : Type*) [Magma G] (h : Equation23077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X0) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X4 ◇ X0))) = X6 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ X3) := superpose eq7 eq10
  have eq48 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq10 eq17
  have eq160 (X0 X5 : G) : X0 = X5 := superpose eq7 eq48
  have eq323 (X0 : G) : sK0 ≠ X0 := superpose eq160 eq8
  subsumption eq323 eq160


@[equational_result]
theorem Equation23078_implies_Equation2 (G : Type*) [Magma G] (h : Equation23078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X0) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 X6 X7 : G) : ((X1 ◇ X0) ◇ ((X6 ◇ X7) ◇ ((X5 ◇ X0) ◇ X4))) = X7 := superpose eq7 eq7
  have eq10 (X0 X3 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ X3)) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X7 : G) : ((X1 ◇ X0) ◇ X0) = X7 := superpose eq10 eq9
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation23079_implies_Equation2 (G : Type*) [Magma G] (h : Equation23079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X0) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : (X0 ◇ ((X5 ◇ X6) ◇ X5)) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation23080_implies_Equation2 (G : Type*) [Magma G] (h : Equation23080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X0) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X6 X7 X8 : G) : (X0 ◇ ((X6 ◇ X7) ◇ X8)) = X7 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq36 (X0 X6 : G) : X0 = X6 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation23082_implies_Equation2 (G : Type*) [Magma G] (h : Equation23082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23083_implies_Equation2 (G : Type*) [Magma G] (h : Equation23083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X1) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23084_implies_Equation2 (G : Type*) [Magma G] (h : Equation23084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X1) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23085_implies_Equation2 (G : Type*) [Magma G] (h : Equation23085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X1) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23086_implies_Equation2 (G : Type*) [Magma G] (h : Equation23086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X1) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23088_implies_Equation2 (G : Type*) [Magma G] (h : Equation23088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23089_implies_Equation2 (G : Type*) [Magma G] (h : Equation23089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X2) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23090_implies_Equation2 (G : Type*) [Magma G] (h : Equation23090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X2) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23091_implies_Equation2 (G : Type*) [Magma G] (h : Equation23091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X2) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23092_implies_Equation2 (G : Type*) [Magma G] (h : Equation23092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X2) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23094_implies_Equation2 (G : Type*) [Magma G] (h : Equation23094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23095_implies_Equation2 (G : Type*) [Magma G] (h : Equation23095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23096_implies_Equation2 (G : Type*) [Magma G] (h : Equation23096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23097_implies_Equation2 (G : Type*) [Magma G] (h : Equation23097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23098_implies_Equation2 (G : Type*) [Magma G] (h : Equation23098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23100_implies_Equation2 (G : Type*) [Magma G] (h : Equation23100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X4) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23101_implies_Equation2 (G : Type*) [Magma G] (h : Equation23101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X4) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23102_implies_Equation2 (G : Type*) [Magma G] (h : Equation23102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X4) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23103_implies_Equation2 (G : Type*) [Magma G] (h : Equation23103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X4) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23104_implies_Equation2 (G : Type*) [Magma G] (h : Equation23104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X4) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23106_implies_Equation2 (G : Type*) [Magma G] (h : Equation23106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X5) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23107_implies_Equation2 (G : Type*) [Magma G] (h : Equation23107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X5) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23108_implies_Equation2 (G : Type*) [Magma G] (h : Equation23108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X5) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23109_implies_Equation2 (G : Type*) [Magma G] (h : Equation23109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X5) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23110_implies_Equation2 (G : Type*) [Magma G] (h : Equation23110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X5) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23111_implies_Equation2 (G : Type*) [Magma G] (h : Equation23111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X5) ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23327_implies_Equation2 (G : Type*) [Magma G] (h : Equation23327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq7 eq11
  have eq26 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq10
  have eq39 (X0 : G) : (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq11 eq26
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq26
  have eq52 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq43 eq39
  have eq55 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq43 eq52
  have eq104 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq55 eq7
  have eq112 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq43 eq104
  have eq145 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq7 eq43
  have eq146 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq26 eq43
  have eq175 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := superpose eq146 eq145
  have eq179 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq175 eq12
  have eq231 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq175 eq179
  have eq232 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)) := superpose eq175 eq231
  have eq233 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) := superpose eq112 eq232
  have eq234 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq43 eq233
  have eq235 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := superpose eq234 eq11
  have eq240 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq234 eq235
  have eq241 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq240 eq43
  have eq313 (X0 X2 : G) : X0 = X2 := superpose eq241 eq241
  have eq333 (X0 : G) : sK0 ≠ X0 := superpose eq313 eq8
  subsumption eq333 eq313


@[equational_result]
theorem Equation23330_implies_Equation2 (G : Type*) [Magma G] (h : Equation23330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq11
  have eq17 (X0 X1 X2 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X2 := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq11
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2))) := superpose eq11 eq7
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3))) := superpose eq7 eq9
  have eq32 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X3))) := superpose eq11 eq9
  have eq41 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X3))) := superpose eq20 eq32
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq7 eq12
  have eq53 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq11 eq12
  have eq54 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq12
  have eq63 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq10 eq52
  have eq64 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq20 eq53
  have eq65 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X3))) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq64 eq41
  have eq93 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq12 eq16
  have eq96 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)))) := superpose eq11 eq16
  have eq128 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) := superpose eq11 eq18
  have eq145 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) := superpose eq18 eq9
  have eq147 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := superpose eq18 eq7
  have eq163 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) := superpose eq7 eq145
  have eq164 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq7 eq147
  have eq165 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq164 eq163
  have eq168 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq164 eq165
  have eq171 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq168 eq63
  have eq172 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq168 eq10
  have eq179 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq168 eq64
  have eq184 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq168 eq171
  have eq189 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq184 eq93
  have eq196 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq184 eq172
  have eq208 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq196 eq189
  have eq213 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq196 eq96
  have eq226 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X3))) := superpose eq179 eq65
  have eq239 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq7 eq184
  have eq241 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) = ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq9 eq184
  have eq249 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := superpose eq184 eq12
  have eq251 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq184 eq7
  have eq259 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq184 eq11
  have eq260 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X3))) := superpose eq239 eq226
  have eq262 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq239 eq213
  have eq265 (X0 X1 X2 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X2 := superpose eq262 eq17
  have eq271 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq249 eq208
  have eq275 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq196 eq251
  have eq276 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq275 eq54
  have eq283 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq196 eq259
  have eq284 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) := superpose eq283 eq128
  have eq376 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0)) := superpose eq11 eq265
  have eq382 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq184 eq265
  have eq399 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2))) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq265 eq12
  have eq417 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq284 eq382
  have eq418 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) = X1 := superpose eq11 eq417
  have eq419 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) := superpose eq418 eq260
  have eq420 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq419 eq376
  have eq425 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq418 eq399
  have eq426 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X1 := superpose eq418 eq425
  have eq427 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq426 eq420
  have eq428 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq426 eq427
  have eq430 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq428 eq271
  have eq462 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq430 eq276
  have eq468 (X0 X1 X3 : G) : (X0 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3))) = X1 := superpose eq462 eq26
  have eq481 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq462 eq241
  have eq488 (X0 X1 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq462 eq468
  have eq506 (X0 X2 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq462 eq481
  have eq507 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq506 eq428
  have eq512 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X1 := superpose eq506 eq488
  have eq518 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq507 eq506
  have eq528 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq518 eq512
  have eq529 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq518 eq528
  have eq559 (X0 X2 : G) : X0 = X2 := superpose eq529 eq529
  have eq561 (X0 : G) : sK0 ≠ X0 := superpose eq559 eq8
  subsumption eq561 eq559


@[equational_result]
theorem Equation23332_implies_Equation2 (G : Type*) [Magma G] (h : Equation23332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) = ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq12 eq7
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2)) := superpose eq11 eq11
  have eq24 (X0 X1 X2 X3 : G) : ((((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq11 eq7
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq12
  have eq115 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (X2 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) = X0 := superpose eq16 eq10
  have eq121 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X3 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))))) := superpose eq10 eq9
  have eq132 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq115 eq121
  have eq134 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq132 eq10
  have eq135 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := superpose eq134 eq18
  have eq136 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq134 eq135
  have eq139 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq136 eq25
  have eq140 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq134 eq139
  have eq142 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq140 eq24
  have eq154 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq140 eq142
  have eq155 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0) = X3 := superpose eq140 eq154
  have eq156 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X3 := superpose eq140 eq155
  have eq204 (X0 X4 : G) : X0 = X4 := superpose eq156 eq156
  have eq281 (X0 : G) : sK0 ≠ X0 := superpose eq204 eq8
  subsumption eq281 eq204


@[equational_result]
theorem Equation23334_implies_Equation2 (G : Type*) [Magma G] (h : Equation23334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X4 ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq32 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq42 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq32 eq11
  have eq47 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq32 eq42
  have eq64 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X4 ◇ X5))) := superpose eq7 eq9
  have eq73 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X4))) := superpose eq32 eq9
  have eq94 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X3 ◇ X4))) := superpose eq32 eq73
  have eq95 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X3 ◇ X4))) := superpose eq47 eq94
  have eq96 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq47 eq95
  have eq97 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X4 ◇ X5))) := superpose eq96 eq64
  have eq116 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq96 eq97
  have eq117 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = (X0 ◇ X1) := superpose eq96 eq116
  have eq118 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq96 eq117
  have eq119 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq118 eq11
  have eq131 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq118 eq119
  have eq182 (X0 X1 : G) : X0 = X1 := superpose eq131 eq118
  have eq184 (X0 : G) : sK0 ≠ X0 := superpose eq182 eq8
  subsumption eq184 eq182


@[equational_result]
theorem Equation23336_implies_Equation2 (G : Type*) [Magma G] (h : Equation23336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) := superpose eq7 eq11
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11
  have eq20 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq11 eq7
  have eq21 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((((X2 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X4 ◇ ((X1 ◇ X0) ◇ (((X3 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq7 eq9
  have eq31 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq11 eq9
  have eq39 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (X0 ◇ (X4 ◇ ((X1 ◇ X0) ◇ (((X3 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq20 eq21
  have eq42 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq20 eq31
  have eq43 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq16 eq42
  have eq44 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq16 eq43
  have eq45 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X1))) = X0 := superpose eq16 eq44
  have eq49 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq45 eq14
  have eq57 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = (X0 ◇ (X4 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq49 eq39
  have eq63 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = (X0 ◇ (X4 ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))))) := superpose eq49 eq57
  have eq64 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = (X0 ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq49 eq63
  have eq65 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = (X0 ◇ (X4 ◇ (X0 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)))) := superpose eq49 eq64
  have eq66 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq45 eq65
  have eq69 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := superpose eq66 eq7
  have eq85 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq66 eq69
  have eq86 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq66 eq85
  have eq87 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq66 eq86
  have eq94 (X0 X1 : G) : X0 = X1 := superpose eq87 eq66
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq96 eq94


@[equational_result]
theorem Equation23338_implies_Equation2 (G : Type*) [Magma G] (h : Equation23338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq11 eq11
  have eq19 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq13 eq11
  have eq24 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq19 eq13
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq37 eq27


@[equational_result]
theorem Equation23340_implies_Equation2 (G : Type*) [Magma G] (h : Equation23340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq12 eq12
  have eq23 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq15 eq12
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq15 eq23
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq44 eq33


@[equational_result]
theorem Equation23342_implies_Equation2 (G : Type*) [Magma G] (h : Equation23342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq12 eq11
  have eq16 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq24 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq16 eq12
  have eq27 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq24 eq13
  have eq30 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq24 eq27
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq36 eq31


@[equational_result]
theorem Equation23345_implies_Equation2 (G : Type*) [Magma G] (h : Equation23345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ (X3 ◇ X3))) := superpose eq7 eq9
  have eq33 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq19
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq33 eq33
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq91 eq59


@[equational_result]
theorem Equation23346_implies_Equation2 (G : Type*) [Magma G] (h : Equation23346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq15 eq12
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq22 eq15
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq49 eq30


@[equational_result]
theorem Equation23348_implies_Equation2 (G : Type*) [Magma G] (h : Equation23348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ X5) = X4 := superpose eq7 eq12
  have eq16 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq12 eq12
  have eq23 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq16 eq13
  have eq30 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq23 eq16
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq51 eq32


@[equational_result]
theorem Equation23349_implies_Equation2 (G : Type*) [Magma G] (h : Equation23349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq21 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq14 eq12
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq21 eq14
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq49 eq30


@[equational_result]
theorem Equation23350_implies_Equation2 (G : Type*) [Magma G] (h : Equation23350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq21 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq14 eq12
  have eq26 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq21 eq14
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq47 eq28


@[equational_result]
theorem Equation23351_implies_Equation2 (G : Type*) [Magma G] (h : Equation23351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq21 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq14 eq12
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq21 eq14
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq49 eq30


@[equational_result]
theorem Equation23359_implies_Equation2 (G : Type*) [Magma G] (h : Equation23359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X4 : G) : ((((X1 ◇ X0) ◇ X4) ◇ (X1 ◇ X0)) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq10
  have eq16 (X0 X1 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) = X3 := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X2) = (((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ ((X2 ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4))) ◇ X0) := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((((X3 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq7 eq11
  have eq28 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ X0) ◇ X2) := superpose eq10 eq11
  have eq34 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X3 ◇ (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ X0))))) = X1 := superpose eq11 eq7
  have eq61 (X0 X1 X2 X4 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = ((X2 ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq11 eq9
  have eq79 (X0 X1 X2 X4 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X4 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) = X4 := superpose eq9 eq10
  have eq126 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ X0))) = (((((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ X0)))) ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) := superpose eq11 eq28
  have eq135 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇ (X0 ◇ (X1 ◇ X2))) = ((((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X4) := superpose eq9 eq28
  have eq272 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ ((X1 ◇ X0) ◇ X1))))) := superpose eq79 eq79
  have eq284 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq16 eq79
  have eq285 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq7 eq79
  have eq295 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X2) := superpose eq79 eq11
  have eq330 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq9 eq272
  have eq1480 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq330 eq23
  have eq1603 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq330 eq1480
  have eq1606 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ X1)) = ((X2 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq18 eq1603
  have eq1629 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1))) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq1603 eq1603
  have eq1638 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq1603 eq28
  have eq1647 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq1603 eq7
  have eq1654 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1)) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq1603 eq285
  have eq1685 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq330 eq1638
  have eq1691 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1)) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq1629 eq1654
  have eq1692 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1))) := superpose eq1691 eq1629
  have eq1693 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1)) = ((((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq1692 eq1691
  have eq1696 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X2 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X1)) := superpose eq1647 eq1693
  have eq1967 (X0 X1 X2 X3 : G) : (((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)))) = ((((X2 ◇ (((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))))) ◇ X2) ◇ (((X1 ◇ X2) ◇ ((X2 ◇ (((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))))) ◇ X2)) ◇ (X1 ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq23 eq34
  have eq2213 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = (((X3 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq1696 eq1696
  have eq2227 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2)) := superpose eq1696 eq14
  have eq2251 (X0 X1 X2 X3 : G) : ((((X2 ◇ X1) ◇ X3) ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X3 := superpose eq1696 eq7
  have eq2266 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X3 ◇ (X2 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq330 eq2213
  have eq2348 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) = ((((X2 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)))) ◇ X2) ◇ (((X1 ◇ X2) ◇ ((X2 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)))) ◇ X2)) ◇ (X1 ◇ X2))) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq2266 eq1967
  have eq2452 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ X2) := superpose eq2227 eq295
  have eq2456 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = ((((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2) := superpose eq330 eq2452
  have eq2672 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq16 eq2251
  have eq2888 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ X1) := superpose eq7 eq2672
  have eq5106 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq2227 eq61
  have eq5120 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq1606 eq5106
  have eq5289 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq5120 eq28
  have eq5331 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X2 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X2 ◇ X0)) := superpose eq5120 eq1696
  have eq5401 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq2888 eq5289
  have eq5434 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ X0))) = ((((X0 ◇ X1) ◇ X0) ◇ (((X2 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) := superpose eq5331 eq126
  have eq6012 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq5401 eq14
  have eq6060 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq5401 eq6012
  have eq6121 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X0 := superpose eq6060 eq284
  have eq6124 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X0 := superpose eq6060 eq2672
  have eq6179 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose eq6124 eq2456
  have eq6189 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇ (X0 ◇ (X1 ◇ X2))) = ((((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4) := superpose eq6179 eq135
  have eq6243 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X4) ◇ (X0 ◇ (X1 ◇ X2))) = X4 := superpose eq6124 eq6189
  have eq6244 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq6243 eq6121
  have eq6245 (X0 X3 : G) : (X3 ◇ (X3 ◇ X0)) = X3 := superpose eq6243 eq10
  have eq6884 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq6245 eq1685
  have eq6888 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq6244 eq6884
  have eq6889 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq6245 eq6888
  have eq6970 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq6889 eq5434
  have eq7004 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) = (((X2 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)))) ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq6889 eq2348
  have eq7398 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq6889 eq7004
  have eq7399 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7398 eq6970
  have eq10775 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq6245 eq7399
  have eq10782 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq6244 eq10775
  have eq10797 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X4) ◇ (X0 ◇ X1)) = X4 := superpose eq10782 eq6243
  have eq10890 (X0 X4 : G) : ((X0 ◇ X4) ◇ X0) = X4 := superpose eq10782 eq10797
  have eq10891 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq10782 eq10890
  have eq10901 (X0 X2 : G) : X0 = X2 := superpose eq10891 eq10891
  have eq10921 (X0 : G) : sK0 ≠ X0 := superpose eq10901 eq8
  subsumption eq10921 eq10901


@[equational_result]
theorem Equation23361_implies_Equation2 (G : Type*) [Magma G] (h : Equation23361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq11 eq11
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq11
  have eq29 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq42 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq16 eq16
  have eq43 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq16 eq7
  have eq51 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq43 eq29
  have eq53 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ X3)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5))) := superpose eq51 eq9
  have eq57 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq51 eq14
  have eq60 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5))) := superpose eq42 eq53
  have eq63 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq42 eq57
  have eq77 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq10 eq60
  have eq84 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq16 eq77
  have eq89 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq84 eq63
  have eq93 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq89 eq51
  have eq97 (X0 X1 : G) : X0 = X1 := superpose eq89 eq93
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq102 eq97


@[equational_result]
theorem Equation23364_implies_Equation2 (G : Type*) [Magma G] (h : Equation23364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X2))) = X1 := superpose eq11 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) = (((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2))) ◇ X3) ◇ (X3 ◇ (X2 ◇ X1))) := superpose eq10 eq10
  have eq27 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = ((((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq10 eq11
  have eq29 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X2 ◇ X1) ◇ X3))) := superpose eq10 eq7
  have eq45 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq9 eq9
  have eq340 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq45 eq29
  have eq384 (X0 X1 X2 : G) : (X0 ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq340 eq29
  have eq385 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq340 eq10
  have eq415 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) ◇ ((((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)))) := superpose eq340 eq45
  have eq423 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq15 eq415
  have eq427 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq423 eq384
  have eq774 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2) ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)))) = (((X4 ◇ (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2) ◇ ((((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2)) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))))) ◇ X4) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq45 eq18
  have eq872 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq427 eq7
  have eq886 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := superpose eq427 eq11
  have eq1157 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq385 eq423
  have eq1782 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) = X0 := superpose eq872 eq1157
  have eq1985 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq1782 eq7
  have eq1987 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) ◇ (X1 ◇ X0)) := superpose eq1782 eq7
  have eq2318 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = (((X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq1782 eq27
  have eq2807 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq340 eq1987
  have eq3656 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq2807
  have eq3881 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = X0 := superpose eq3656 eq10
  have eq3931 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq3881 eq385
  have eq3940 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq3931 eq1157
  have eq3995 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2) ◇ ((X0 ◇ ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2)) ◇ X0)) = (((X4 ◇ (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2) ◇ ((X0 ◇ ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2)) ◇ X0))) ◇ X4) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := superpose eq3940 eq774
  have eq5528 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2) ◇ ((X0 ◇ ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2)) ◇ X0)) = (((X4 ◇ (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2) ◇ ((X0 ◇ ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3)))) ◇ X2)) ◇ X0))) ◇ X4) ◇ (X4 ◇ X1)) := superpose eq3940 eq3995
  have eq5529 (X0 X1 X4 : G) : (((X4 ◇ X0) ◇ X4) ◇ (X4 ◇ X1)) = X0 := superpose eq3940 eq5528
  have eq5531 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq5529 eq1985
  have eq5533 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq3940 eq5531
  have eq5534 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq5533 eq2318
  have eq5546 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = X0 := superpose eq5529 eq5534
  have eq5547 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq5533 eq5546
  have eq5549 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := superpose eq5547 eq886
  have eq5553 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := superpose eq5547 eq5549
  have eq5554 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq5553 eq427
  have eq5557 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq5554 eq3931
  have eq5561 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose eq5557 eq11
  have eq5585 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq3940 eq5561
  have eq5586 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq5585 eq7
  have eq5623 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq5585 eq5586
  have eq5624 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq5585 eq5623
  have eq5706 (X0 X2 : G) : X0 = X2 := superpose eq5624 eq5624
  have eq5708 (X0 : G) : sK0 ≠ X0 := superpose eq5706 eq8
  subsumption eq5708 eq5706


@[equational_result]
theorem Equation23367_implies_Equation2 (G : Type*) [Magma G] (h : Equation23367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X3))) := superpose eq10 eq10
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq10 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq10 eq7
  have eq31 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq7 eq14
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq14 eq7
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq40 eq16
  have eq52 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) := superpose eq14 eq9
  have eq73 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq7 eq52
  have eq76 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq73 eq13
  have eq87 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq73 eq42
  have eq121 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq76 eq87
  have eq124 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq121 eq31
  have eq139 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq121 eq124
  have eq140 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq139 eq73
  have eq146 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq139 eq140
  have eq147 (X0 X3 : G) : X0 = X3 := superpose eq146 eq146
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq147 eq8
  subsumption eq152 eq147


@[equational_result]
theorem Equation23369_implies_Equation2 (G : Type*) [Magma G] (h : Equation23369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0) = X2 := superpose eq12 eq12
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X0)) = X2 := superpose eq12 eq7
  have eq36 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq18 eq18
  have eq59 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq36 eq14
  have eq60 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq59 eq12
  have eq63 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq36 eq60
  have eq64 (X0 X3 : G) : X0 = X3 := superpose eq7 eq63
  have eq97 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq97 eq64


@[equational_result]
theorem Equation23371_implies_Equation2 (G : Type*) [Magma G] (h : Equation23371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4))) = X2 := superpose eq7 eq7
  have eq36 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq10 eq10
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq36
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq110 eq47


@[equational_result]
theorem Equation23373_implies_Equation2 (G : Type*) [Magma G] (h : Equation23373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq11 eq7
  have eq48 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq18 eq18
  have eq97 (X0 X3 : G) : X0 = X3 := superpose eq7 eq48
  have eq199 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq199 eq97


@[equational_result]
theorem Equation23375_implies_Equation2 (G : Type*) [Magma G] (h : Equation23375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq11 eq11
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq116 eq34


@[equational_result]
theorem Equation23377_implies_Equation2 (G : Type*) [Magma G] (h : Equation23377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq11 eq11
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq13 eq11
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq13 eq19
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation23379_implies_Equation2 (G : Type*) [Magma G] (h : Equation23379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq7 eq12
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq12
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation23382_implies_Equation2 (G : Type*) [Magma G] (h : Equation23382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq10 eq7
  have eq22 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := superpose eq9 eq9
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2)))) = X4 := superpose eq9 eq7
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq22 eq7
  have eq240 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X3))) = X1 := superpose eq42 eq10
  have eq397 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X3 ◇ X3))) = (X1 ◇ ((X2 ◇ X1) ◇ X2)) := superpose eq24 eq7
  have eq561 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X3) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) ◇ (X4 ◇ (X4 ◇ X4))) := superpose eq397 eq7
  have eq613 (X0 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X3) = (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X4 ◇ (X4 ◇ X4))) := superpose eq11 eq561
  have eq6473 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ X0) := superpose eq7 eq613
  have eq6928 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq6473 eq6473
  have eq7009 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq6473 eq613
  have eq7219 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq6928 eq7009
  have eq7220 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq10 eq7219
  have eq7221 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X2))) = X0 := superpose eq7220 eq7
  have eq7687 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X3 ◇ (X3 ◇ X3))) = X1 := superpose eq7221 eq240
  have eq7723 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq7687 eq42
  have eq7724 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq7723 eq10
  have eq7751 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq7723 eq7724
  have eq7752 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7723 eq7751
  have eq7753 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7752 eq7220
  have eq7785 (X0 X1 : G) : X0 = X1 := superpose eq7752 eq7753
  have eq7815 (X0 : G) : sK0 ≠ X0 := superpose eq7785 eq8
  subsumption eq7815 eq7785


@[equational_result]
theorem Equation23383_implies_Equation2 (G : Type*) [Magma G] (h : Equation23383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq7 eq12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq16 eq12
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation23385_implies_Equation2 (G : Type*) [Magma G] (h : Equation23385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1))))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X0) ◇ X5) = X4 := superpose eq7 eq12
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq7 eq12
  have eq23 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq17 eq15
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))) = X1 := superpose eq23 eq10
  have eq32 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq23 eq30
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq32 eq32
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq35 eq33


@[equational_result]
theorem Equation23386_implies_Equation2 (G : Type*) [Magma G] (h : Equation23386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq12 eq12
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq15 eq14
  have eq23 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq15 eq12
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq23 eq21
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq35 eq30


@[equational_result]
theorem Equation23387_implies_Equation2 (G : Type*) [Magma G] (h : Equation23387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) = X1 := superpose eq7 eq7
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq49 eq33


@[equational_result]
theorem Equation23388_implies_Equation2 (G : Type*) [Magma G] (h : Equation23388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X4 ◇ X5))) = X2 := superpose eq7 eq7
  have eq33 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq53 eq33


@[equational_result]
theorem Equation23390_implies_Equation2 (G : Type*) [Magma G] (h : Equation23390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X1))) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1))) := superpose eq10 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X1))) = X2 := superpose eq10 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq10 eq9
  have eq43 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X2) ◇ X0) := superpose eq15 eq35
  have eq45 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X1))) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq43 eq19
  have eq50 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X1))) = ((X0 ◇ X3) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq43 eq45
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq20 eq50
  have eq52 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq51 eq10
  have eq53 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq52 eq7
  have eq62 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq52 eq53
  have eq63 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X0 := superpose eq52 eq62
  have eq64 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq52 eq63
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq64 eq64
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq67 eq65


@[equational_result]
theorem Equation23391_implies_Equation2 (G : Type*) [Magma G] (h : Equation23391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq25 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq10 eq9
  have eq39 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq25
  have eq49 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq25 eq7
  have eq145 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq39
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq25 eq39
  have eq175 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ X0) ◇ X1) := superpose eq148 eq145
  have eq179 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X0)) := superpose eq175 eq49
  have eq228 (X0 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X0)) := superpose eq175 eq179
  have eq229 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X2 ◇ X0)) := superpose eq25 eq228
  have eq230 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq39 eq229
  have eq233 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq230 eq25
  have eq243 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq230 eq233
  have eq319 (X0 X2 : G) : X0 = X2 := superpose eq243 eq243
  have eq324 (X0 : G) : sK0 ≠ X0 := superpose eq319 eq8
  subsumption eq324 eq319


@[equational_result]
theorem Equation23392_implies_Equation2 (G : Type*) [Magma G] (h : Equation23392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq13 eq10
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq20 eq13
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq38 eq28


@[equational_result]
theorem Equation23394_implies_Equation2 (G : Type*) [Magma G] (h : Equation23394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq7 eq10
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = ((X0 ◇ X3) ◇ ((X0 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) ◇ (X1 ◇ X1))) := superpose eq10 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq10 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq14 eq11
  have eq20 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq18 eq19
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := superpose eq10 eq20
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq20 eq7
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = ((X0 ◇ X3) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq22 eq17
  have eq34 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = X1 := superpose eq18 eq33
  have eq36 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq34 eq10
  have eq39 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq18 eq27
  have eq40 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq39 eq7
  have eq51 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq39 eq40
  have eq52 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq39 eq51
  have eq53 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq39 eq52
  have eq64 (X0 X1 : G) : X0 = X1 := superpose eq53 eq36
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq69 eq64


@[equational_result]
theorem Equation23396_implies_Equation2 (G : Type*) [Magma G] (h : Equation23396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X4))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq26 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq15 eq10
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq58 eq33


@[equational_result]
theorem Equation23399_implies_Equation2 (G : Type*) [Magma G] (h : Equation23399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X0) = (((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq7 eq9
  have eq21 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq9
  have eq23 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq9 eq10
  have eq24 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq7
  have eq26 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq23
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq24 eq21
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ ((((X2 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ ((((X2 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X2 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ X0))))))) := superpose eq10 eq19
  have eq62 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)))) = X1 := superpose eq11 eq10
  have eq75 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq27 eq19
  have eq76 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq27 eq9
  have eq89 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq27 eq75
  have eq90 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq26 eq89
  have eq91 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq90
  have eq97 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq91 eq27
  have eq107 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq97 eq11
  have eq110 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))))) := superpose eq107 eq32
  have eq115 (X1 X2 : G) : (((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X1 := superpose eq107 eq62
  have eq119 (X1 X2 : G) : (((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq91 eq115
  have eq120 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq97 eq119
  have eq134 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq91 eq76
  have eq156 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq107 eq7
  have eq163 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq134 eq156
  have eq164 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq120 eq163
  have eq167 (X0 X2 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2)))) = X2 := superpose eq164 eq10
  have eq177 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))))) = X1 := superpose eq164 eq110
  have eq189 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq164 eq167
  have eq202 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))))) = X1 := superpose eq164 eq177
  have eq203 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := superpose eq164 eq202
  have eq204 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq164 eq203
  have eq205 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq189 eq204
  have eq253 (X0 X2 : G) : X0 = X2 := superpose eq205 eq205
  have eq266 (X0 : G) : sK0 ≠ X0 := superpose eq253 eq8
  subsumption eq266 eq253


@[equational_result]
theorem Equation23400_implies_Equation2 (G : Type*) [Magma G] (h : Equation23400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X4))) = X0 := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq24 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq18 eq16
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq24 eq18
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq50 eq36


@[equational_result]
theorem Equation23402_implies_Equation2 (G : Type*) [Magma G] (h : Equation23402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X2 ◇ (X4 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq18 eq17
  have eq30 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ (X4 ◇ X0))) = X2 := superpose eq29 eq10
  have eq35 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X2 := superpose eq29 eq30
  have eq36 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq29 eq35
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq36 eq36
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation23403_implies_Equation2 (G : Type*) [Magma G] (h : Equation23403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ (X4 ◇ (X0 ◇ (X3 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X4 ◇ X0)))) ◇ X0) = X2 := superpose eq10 eq7
  have eq48 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X3 ◇ X4))) = ((X0 ◇ X1) ◇ X0) := superpose eq11 eq17
  have eq49 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq17 eq17
  have eq62 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X0) = X2 := superpose eq48 eq20
  have eq63 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq49 eq62
  have eq103 (X0 X4 : G) : X0 = X4 := superpose eq7 eq63
  have eq215 (X0 : G) : sK0 ≠ X0 := superpose eq103 eq8
  subsumption eq215 eq103


@[equational_result]
theorem Equation23404_implies_Equation2 (G : Type*) [Magma G] (h : Equation23404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ (X4 ◇ X4))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq20 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq12 eq10
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation23405_implies_Equation2 (G : Type*) [Magma G] (h : Equation23405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ (X2 ◇ (X5 ◇ X6))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq21 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq13 eq10
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation23407_implies_Equation2 (G : Type*) [Magma G] (h : Equation23407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq10 eq7
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq18 eq18
  have eq94 (X0 X3 : G) : X0 = X3 := superpose eq7 eq42
  have eq196 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq196 eq94


@[equational_result]
theorem Equation23409_implies_Equation2 (G : Type*) [Magma G] (h : Equation23409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq115 eq39


@[equational_result]
theorem Equation23411_implies_Equation2 (G : Type*) [Magma G] (h : Equation23411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation23413_implies_Equation2 (G : Type*) [Magma G] (h : Equation23413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X4))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation23416_implies_Equation2 (G : Type*) [Magma G] (h : Equation23416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X2)) = ((X0 ◇ X3) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq11 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3))) = X2 := superpose eq11 eq7
  have eq57 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((((X2 ◇ X2) ◇ X0) ◇ X2) ◇ (X1 ◇ X1))) = ((X3 ◇ (X2 ◇ X2)) ◇ X3) := superpose eq9 eq13
  have eq64 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X3 ◇ X3)) = (((X0 ◇ X1) ◇ (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X1))) ◇ X2) := superpose eq9 eq13
  have eq86 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X1 := superpose eq13 eq7
  have eq98 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X2) = (X3 ◇ ((X4 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ ((((X2 ◇ X2) ◇ X0) ◇ X2) ◇ (X1 ◇ X1)))) ◇ (X4 ◇ ((X0 ◇ X1) ◇ ((((X2 ◇ X2) ◇ X0) ◇ X2) ◇ (X1 ◇ X1))))))) := superpose eq9 eq10
  have eq194 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose eq13 eq14
  have eq213 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq86 eq194
  have eq214 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq213 eq13
  have eq247 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ ((((X2 ◇ X2) ◇ X0) ◇ X2) ◇ (X1 ◇ X1))) := superpose eq214 eq57
  have eq285 (X2 X3 X4 : G) : (X2 ◇ X2) = (X3 ◇ ((X4 ◇ X3) ◇ ((X4 ◇ (X2 ◇ X2)) ◇ (X4 ◇ (X2 ◇ X2))))) := superpose eq247 eq98
  have eq289 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq10 eq285
  have eq291 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3))) = (X1 ◇ X2) := superpose eq289 eq9
  have eq292 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X2 := superpose eq289 eq10
  have eq295 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) ◇ (X3 ◇ X3))) = X2 := superpose eq289 eq15
  have eq319 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ (X3 ◇ X3)) = (((X0 ◇ X1) ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) ◇ X2) := superpose eq289 eq64
  have eq349 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ X3) ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) := superpose eq289 eq291
  have eq350 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq289 eq292
  have eq352 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq289 eq295
  have eq402 (X2 X3 : G) : ((X3 ◇ X3) ◇ (X3 ◇ X3)) = ((X2 ◇ X3) ◇ X2) := superpose eq349 eq319
  have eq403 (X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X3) ◇ X2) := superpose eq289 eq402
  have eq404 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq289 eq403
  have eq407 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) = X2 := superpose eq404 eq352
  have eq414 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq407 eq349
  have eq416 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = X2 := superpose eq414 eq350
  have eq430 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq414 eq416
  have eq431 (X0 X3 : G) : X0 = X3 := superpose eq430 eq430
  have eq436 (X0 : G) : sK0 ≠ X0 := superpose eq431 eq8
  subsumption eq436 eq431


@[equational_result]
theorem Equation23417_implies_Equation2 (G : Type*) [Magma G] (h : Equation23417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) = X2 := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq7 eq35
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq124 eq43


@[equational_result]
theorem Equation23419_implies_Equation2 (G : Type*) [Magma G] (h : Equation23419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X4 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq51 eq21


@[equational_result]
theorem Equation23420_implies_Equation2 (G : Type*) [Magma G] (h : Equation23420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X4 ◇ (X1 ◇ (X3 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq27 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq21 eq19
  have eq30 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ (X4 ◇ X2)) ◇ X0) = X3 := superpose eq21 eq12
  have eq39 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq21 eq30
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq39 eq27
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq58 eq44


@[equational_result]
theorem Equation23421_implies_Equation2 (G : Type*) [Magma G] (h : Equation23421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X4 ◇ X4))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq52 eq19


@[equational_result]
theorem Equation23422_implies_Equation2 (G : Type*) [Magma G] (h : Equation23422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X5 ◇ X6))) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq53 eq22


@[equational_result]
theorem Equation23425_implies_Equation2 (G : Type*) [Magma G] (h : Equation23425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = ((X0 ◇ X3) ◇ (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X3 ◇ (X0 ◇ X3))) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0))))) ◇ (((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X0)) = X2 := superpose eq10 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0))))))) := superpose eq10 eq9
  have eq21 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) = ((X1 ◇ X2) ◇ (X2 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X2))) := superpose eq10 eq9
  have eq28 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = (((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3))) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq9 eq7
  have eq41 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X1 ◇ X2))) := superpose eq11 eq11
  have eq340 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq41 eq28
  have eq388 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq340 eq28
  have eq389 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq340 eq9
  have eq417 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = ((((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))))) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X0 ◇ X1))) := superpose eq340 eq41
  have eq423 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose eq14 eq417
  have eq427 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq423 eq388
  have eq744 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X3) ◇ X2)) = ((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X3)) ◇ ((((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) ◇ ((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X3)) ◇ ((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)))) ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X2)) ◇ (((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0)) ◇ ((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X3)) ◇ ((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0))))))) := superpose eq21 eq18
  have eq754 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) := superpose eq7 eq18
  have eq819 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq427 eq7
  have eq832 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq427 eq10
  have eq1206 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq389 eq423
  have eq1207 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq389 eq340
  have eq1797 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq819 eq1206
  have eq2016 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq1797 eq7
  have eq2890 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq1207 eq2016
  have eq2910 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq2890
  have eq2911 (X0 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0)) = X0 := superpose eq2910 eq754
  have eq3029 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq2910 eq9
  have eq3093 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq3029 eq389
  have eq3107 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq3093 eq1206
  have eq3188 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X3) ◇ X2)) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))))) ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X2)) ◇ (((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0)))))))) := superpose eq3107 eq744
  have eq3381 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq3107 eq2911
  have eq4277 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X3) ◇ X2)) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X3 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X3)) ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X2)) ◇ (X3 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X3))))) := superpose eq3107 eq3188
  have eq4542 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq3381 eq832
  have eq4543 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0) = X0 := superpose eq3107 eq4542
  have eq4544 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq4543 eq427
  have eq4553 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq4544 eq3093
  have eq4569 (X0 X2 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := superpose eq4553 eq10
  have eq4704 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq3107 eq4569
  have eq4710 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X3) ◇ X2)) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X3 ◇ X3) ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X2)) ◇ (X3 ◇ X3)))) := superpose eq4704 eq4277
  have eq4790 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X3) ◇ X2)) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X2 ◇ ((X1 ◇ X3) ◇ X2)) ◇ (X3 ◇ X3))) := superpose eq4704 eq4710
  have eq4791 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X3) ◇ X2)) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ (X3 ◇ X3)) := superpose eq4704 eq4790
  have eq4792 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X3) ◇ X2)) = ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X3) := superpose eq4544 eq4791
  have eq4793 (X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X3) ◇ X2)) = X3 := superpose eq4704 eq4792
  have eq4794 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq4704 eq4793
  have eq4847 (X0 X1 : G) : X0 = X1 := superpose eq4704 eq4794
  have eq4857 (X0 : G) : sK0 ≠ X0 := superpose eq4847 eq8
  subsumption eq4857 eq4847


@[equational_result]
theorem Equation23426_implies_Equation2 (G : Type*) [Magma G] (h : Equation23426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X5))) = X2 := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) = X2 := superpose eq10 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) ◇ (X2 ◇ X5))) = X2 := superpose eq10 eq7
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X5)) = (((X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X5))) ◇ X0) ◇ X3) := superpose eq10 eq12
  have eq41 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X5)) = ((X0 ◇ X0) ◇ X3) := superpose eq14 eq30
  have eq42 (X0 X2 X5 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X2 ◇ X5))) = X2 := superpose eq41 eq22
  have eq43 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq20 eq42
  have eq47 (X0 X1 : G) : X0 = X1 := superpose eq7 eq43
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq120 eq47


@[equational_result]
theorem Equation23430_implies_Equation2 (G : Type*) [Magma G] (h : Equation23430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X4))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X4 ◇ X5) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ X1)))) ◇ X5) = X3 := superpose eq12 eq12
  have eq28 (X0 X1 X2 X3 X7 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X1) ◇ X7))) = X2 := superpose eq10 eq10
  have eq48 (X3 X4 X5 : G) : (X4 ◇ X5) = X3 := superpose eq28 eq14
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq48
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq131 eq49


@[equational_result]
theorem Equation23433_implies_Equation2 (G : Type*) [Magma G] (h : Equation23433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X0 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation23434_implies_Equation2 (G : Type*) [Magma G] (h : Equation23434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4))) = X2 := superpose eq7 eq7
  have eq45 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq90 eq45


@[equational_result]
theorem Equation23436_implies_Equation2 (G : Type*) [Magma G] (h : Equation23436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq7
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq10 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq54 eq43


@[equational_result]
theorem Equation23437_implies_Equation2 (G : Type*) [Magma G] (h : Equation23437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ (X2 ◇ (X3 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq133 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq133 eq8
  subsumption eq157 eq133


@[equational_result]
theorem Equation23438_implies_Equation2 (G : Type*) [Magma G] (h : Equation23438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X4))) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X4)) = X2 := superpose eq11 eq11
  have eq23 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq16 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation23439_implies_Equation2 (G : Type*) [Magma G] (h : Equation23439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X4)) = X2 := superpose eq11 eq11
  have eq23 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq16 eq12
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation23441_implies_Equation2 (G : Type*) [Magma G] (h : Equation23441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq125 eq39


@[equational_result]
theorem Equation23442_implies_Equation2 (G : Type*) [Magma G] (h : Equation23442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq12
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq115 eq39


@[equational_result]
theorem Equation23443_implies_Equation2 (G : Type*) [Magma G] (h : Equation23443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq116 eq34


@[equational_result]
theorem Equation23444_implies_Equation2 (G : Type*) [Magma G] (h : Equation23444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ (X2 ◇ X6))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq10 eq12
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq35 eq27


@[equational_result]
theorem Equation23446_implies_Equation2 (G : Type*) [Magma G] (h : Equation23446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ X4) = X2 := superpose eq7 eq12
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq12
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq39 eq26


@[equational_result]
theorem Equation23447_implies_Equation2 (G : Type*) [Magma G] (h : Equation23447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq12
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq146 eq63


@[equational_result]
theorem Equation23448_implies_Equation2 (G : Type*) [Magma G] (h : Equation23448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ ((X1 ◇ X0) ◇ X4))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq74 eq19


@[equational_result]
theorem Equation23449_implies_Equation2 (G : Type*) [Magma G] (h : Equation23449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X4) ◇ (X5 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X0)) = X3 := superpose eq12 eq11
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq51 eq31


@[equational_result]
theorem Equation23451_implies_Equation2 (G : Type*) [Magma G] (h : Equation23451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 X6 : G) : (((X0 ◇ X4) ◇ X5) ◇ X6) = X4 := superpose eq7 eq12
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation23452_implies_Equation2 (G : Type*) [Magma G] (h : Equation23452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq11
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq139 eq57


@[equational_result]
theorem Equation23453_implies_Equation2 (G : Type*) [Magma G] (h : Equation23453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq12
  have eq22 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq17 eq12
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation23454_implies_Equation2 (G : Type*) [Magma G] (h : Equation23454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X4)) ◇ X6))) = X2 := superpose eq7 eq7
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq43 eq33


@[equational_result]
theorem Equation23456_implies_Equation2 (G : Type*) [Magma G] (h : Equation23456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq56 eq22


@[equational_result]
theorem Equation23457_implies_Equation2 (G : Type*) [Magma G] (h : Equation23457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ (X3 ◇ (X3 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq70 eq20


@[equational_result]
theorem Equation23458_implies_Equation2 (G : Type*) [Magma G] (h : Equation23458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ (X4 ◇ X4))) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation23459_implies_Equation2 (G : Type*) [Magma G] (h : Equation23459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ (X5 ◇ X6))) = X2 := superpose eq7 eq7
  have eq20 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq51 eq20


@[equational_result]
theorem Equation23461_implies_Equation2 (G : Type*) [Magma G] (h : Equation23461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq55 eq22


@[equational_result]
theorem Equation23462_implies_Equation2 (G : Type*) [Magma G] (h : Equation23462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X3 ◇ (X4 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq46 eq35


@[equational_result]
theorem Equation23463_implies_Equation2 (G : Type*) [Magma G] (h : Equation23463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X5))) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation23464_implies_Equation2 (G : Type*) [Magma G] (h : Equation23464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ X6))) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation23465_implies_Equation2 (G : Type*) [Magma G] (h : Equation23465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X6 X7 X8 : G) : (X0 ◇ (X6 ◇ (X7 ◇ X8))) = X2 := superpose eq7 eq7
  have eq19 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation23478_implies_Equation2 (G : Type*) [Magma G] (h : Equation23478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X0) = (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X2 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq7 eq10
  have eq18 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ X1)) = (((((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq10 eq10
  have eq22 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq10 eq11
  have eq23 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq10 eq7
  have eq26 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq10 eq22
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq23 eq18
  have eq33 (X0 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq16 eq16
  have eq36 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq16 eq10
  have eq46 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq27 eq36
  have eq47 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq26 eq46
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq26 eq47
  have eq49 (X0 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq48 eq33
  have eq50 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq26 eq49
  have eq75 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq27 eq10
  have eq93 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq75 eq50
  have eq96 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq93
  have eq105 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ X1)) = (((((X3 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X1))) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq96 eq20
  have eq109 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq96 eq27
  have eq121 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq96 eq75
  have eq135 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X1)) = (((((X3 ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq96 eq105
  have eq136 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X1)) = ((((X3 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq96 eq135
  have eq137 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ X1)) = (((X3 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq96 eq136
  have eq142 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq96 eq109
  have eq169 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq96 eq121
  have eq170 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq142 eq169
  have eq175 (X0 X1 X2 X3 : G) : (((X3 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq170 eq137
  have eq188 (X0 X2 X3 : G) : (((X3 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq170 eq175
  have eq189 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = X2 := superpose eq170 eq188
  have eq190 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq170 eq189
  have eq191 (X0 X3 : G) : X0 = X3 := superpose eq190 eq190
  have eq196 (X0 : G) : sK0 ≠ X0 := superpose eq191 eq8
  subsumption eq196 eq191


@[equational_result]
theorem Equation23481_implies_Equation2 (G : Type*) [Magma G] (h : Equation23481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1))) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq9 eq7
  have eq27 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq7
  have eq43 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X3)) := superpose eq7 eq21
  have eq85 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq43 eq25
  have eq92 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq27 eq85
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := superpose eq92 eq7
  have eq94 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq92 eq9
  have eq115 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq92 eq94
  have eq117 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq115 eq93
  have eq229 (X0 X2 : G) : X0 = X2 := superpose eq117 eq117
  have eq231 (X0 : G) : sK0 ≠ X0 := superpose eq229 eq8
  subsumption eq231 eq229


@[equational_result]
theorem Equation23483_implies_Equation2 (G : Type*) [Magma G] (h : Equation23483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq11 eq7
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq9
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))) = X2 := superpose eq9 eq7
  have eq23 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))))) ◇ X0) := superpose eq9 eq11
  have eq25 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq9 eq11
  have eq37 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq13 eq9
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq13 eq37
  have eq48 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X2 := superpose eq44 eq20
  have eq51 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq44 eq25
  have eq56 (X0 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ X0) := superpose eq44 eq23
  have eq62 (X0 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq48 eq56
  have eq89 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq7 eq19
  have eq96 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq7 eq19
  have eq131 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq96 eq51
  have eq132 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq131 eq62
  have eq137 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) = X2 := superpose eq132 eq48
  have eq139 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq137 eq131
  have eq141 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq139 eq13
  have eq145 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq139 eq44
  have eq159 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq145 eq89
  have eq165 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq145 eq159
  have eq166 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq165 eq141
  have eq170 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq165 eq166
  have eq200 (X0 X2 : G) : X0 = X2 := superpose eq170 eq170
  have eq205 (X0 : G) : sK0 ≠ X0 := superpose eq200 eq8
  subsumption eq205 eq200


@[equational_result]
theorem Equation23484_implies_Equation2 (G : Type*) [Magma G] (h : Equation23484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq9 eq9
  have eq13 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := superpose eq9 eq7
  have eq19 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq9 eq7
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq7 eq13
  have eq27 (X0 X1 X2 X3 : G) : (((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)))) ◇ X3) ◇ (X2 ◇ X2)) = X3 := superpose eq9 eq10
  have eq28 (X0 X1 X2 : G) : (((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1))) ◇ X2) ◇ X1) = X2 := superpose eq10 eq10
  have eq30 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X3 ◇ X3)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) := superpose eq9 eq10
  have eq37 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1)) ◇ X3) ◇ (X2 ◇ X2)) = X3 := superpose eq16 eq27
  have eq38 (X0 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X3) ◇ (X2 ◇ X2)) = X3 := superpose eq20 eq37
  have eq39 (X0 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) ◇ (X2 ◇ X2)) = X3 := superpose eq20 eq38
  have eq41 (X0 X1 X3 : G) : (X1 ◇ X1) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq39 eq30
  have eq42 (X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X2 := superpose eq41 eq28
  have eq54 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq42 eq42
  have eq63 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq54 eq19
  have eq73 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq63 eq12
  have eq95 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X0 := superpose eq42 eq73
  have eq104 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq54 eq95
  have eq105 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq104 eq42
  have eq117 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq104 eq105
  have eq133 (X0 X1 : G) : X0 = X1 := superpose eq117 eq104
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq133 eq8
  subsumption eq147 eq133


@[equational_result]
theorem Equation23485_implies_Equation2 (G : Type*) [Magma G] (h : Equation23485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X4))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq23 (X0 X1 X4 X5 : G) : ((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X4 ◇ X5))) = X0 := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq35 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X4)) := superpose eq9 eq9
  have eq49 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq10 eq31
  have eq53 (X0 X1 : G) : ((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose eq49 eq23
  have eq71 (X0 X1 X5 X6 : G) : (X1 ◇ X0) = (X1 ◇ (X5 ◇ X6)) := superpose eq7 eq35
  have eq75 (X0 X1 X4 X5 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X4 ◇ X5)) = X0 := superpose eq7 eq35
  have eq105 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq75 eq53
  have eq108 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq105 eq10
  have eq112 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq105 eq49
  have eq118 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq112 eq71
  have eq120 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = X2 := superpose eq118 eq108
  have eq122 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq118 eq120
  have eq129 (X0 X2 : G) : X0 = X2 := superpose eq122 eq122
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq131 eq129


@[equational_result]
theorem Equation23487_implies_Equation2 (G : Type*) [Magma G] (h : Equation23487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X2 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq11
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = (((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq11 eq7
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq11 eq7
  have eq19 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq14 eq9
  have eq20 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq18 eq19
  have eq23 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq11 eq20
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq20 eq7
  have eq34 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ (X3 ◇ X0)) := superpose eq23 eq17
  have eq35 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq18 eq34
  have eq36 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq35 eq11
  have eq39 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq18 eq26
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := superpose eq39 eq7
  have eq51 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq39 eq40
  have eq52 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq39 eq51
  have eq53 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq39 eq52
  have eq64 (X0 X1 : G) : X0 = X1 := superpose eq53 eq36
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq69 eq64


@[equational_result]
theorem Equation23489_implies_Equation2 (G : Type*) [Magma G] (h : Equation23489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq11 eq11
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation23491_implies_Equation2 (G : Type*) [Magma G] (h : Equation23491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq11 eq11
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq13 eq11
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq37 eq27


@[equational_result]
theorem Equation23493_implies_Equation2 (G : Type*) [Magma G] (h : Equation23493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq16 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation23496_implies_Equation2 (G : Type*) [Magma G] (h : Equation23496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq7 eq10
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq17 eq17
  have eq329 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq34
  have eq468 (X0 X2 : G) : X0 = X2 := superpose eq329 eq329
  have eq648 (X0 : G) : sK0 ≠ X0 := superpose eq468 eq8
  subsumption eq648 eq468


@[equational_result]
theorem Equation23497_implies_Equation2 (G : Type*) [Magma G] (h : Equation23497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ (X3 ◇ (X3 ◇ X4))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X1 X2 X3 X4 : G) : (X1 ◇ (X3 ◇ (X3 ◇ X4))) = X2 := superpose eq12 eq9
  have eq32 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq52 eq32


@[equational_result]
theorem Equation23499_implies_Equation2 (G : Type*) [Magma G] (h : Equation23499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X2 := superpose eq7 eq12
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq15 eq12
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq41 eq28


@[equational_result]
theorem Equation23500_implies_Equation2 (G : Type*) [Magma G] (h : Equation23500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq12
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation23501_implies_Equation2 (G : Type*) [Magma G] (h : Equation23501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation23502_implies_Equation2 (G : Type*) [Magma G] (h : Equation23502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq12
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation23505_implies_Equation2 (G : Type*) [Magma G] (h : Equation23505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ (((X2 ◇ X2) ◇ X2) ◇ X0)) := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = (((X2 ◇ X2) ◇ X2) ◇ X0) := superpose eq7 eq9
  have eq33 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq7 eq20
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq33 eq33
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq91 eq59


@[equational_result]
theorem Equation23508_implies_Equation2 (G : Type*) [Magma G] (h : Equation23508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq7
  have eq19 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9
  have eq20 (X0 X1 X2 : G) : (((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq10 eq9
  have eq34 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X1 ◇ X2)) = X1 := superpose eq19 eq20
  have eq45 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = X2 := superpose eq27 eq7
  have eq47 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq27 eq7
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq27 eq7
  have eq60 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X1 ◇ X2)) = X1 := superpose eq47 eq34
  have eq61 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X2)) = X1 := superpose eq47 eq19
  have eq62 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) = X1 := superpose eq47 eq60
  have eq71 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = X1 := superpose eq62 eq61
  have eq73 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq71 eq18
  have eq82 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq73 eq49
  have eq83 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X2 := superpose eq82 eq45
  have eq104 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = X2 := superpose eq82 eq83
  have eq105 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X2 := superpose eq82 eq104
  have eq106 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq82 eq105
  have eq128 (X0 X1 : G) : X0 = X1 := superpose eq82 eq106
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq128 eq8
  subsumption eq138 eq128


@[equational_result]
theorem Equation23510_implies_Equation2 (G : Type*) [Magma G] (h : Equation23510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq7 eq10
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq94 eq39


@[equational_result]
theorem Equation23511_implies_Equation2 (G : Type*) [Magma G] (h : Equation23511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ X0) := superpose eq7 eq11
  have eq32 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq17 eq17
  have eq329 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq32
  have eq468 (X0 X2 : G) : X0 = X2 := superpose eq329 eq329
  have eq648 (X0 : G) : sK0 ≠ X0 := superpose eq468 eq8
  subsumption eq648 eq468


@[equational_result]
theorem Equation23512_implies_Equation2 (G : Type*) [Magma G] (h : Equation23512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq27 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq7 eq11
  have eq47 (X0 X2 : G) : X0 = X2 := superpose eq27 eq27
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq110 eq47


@[equational_result]
theorem Equation23515_implies_Equation2 (G : Type*) [Magma G] (h : Equation23515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation23517_implies_Equation2 (G : Type*) [Magma G] (h : Equation23517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation23518_implies_Equation2 (G : Type*) [Magma G] (h : Equation23518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23520_implies_Equation2 (G : Type*) [Magma G] (h : Equation23520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23521_implies_Equation2 (G : Type*) [Magma G] (h : Equation23521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23522_implies_Equation2 (G : Type*) [Magma G] (h : Equation23522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23524_implies_Equation2 (G : Type*) [Magma G] (h : Equation23524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation23525_implies_Equation2 (G : Type*) [Magma G] (h : Equation23525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ X3) = (((X1 ◇ X1) ◇ X1) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = ((X2 ◇ X2) ◇ X2) := superpose eq10 eq7
  have eq22 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq24 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (X4 ◇ (X5 ◇ X4))) = X5 := superpose eq9 eq7
  have eq26 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = (X3 ◇ (((X2 ◇ X2) ◇ X2) ◇ X3)) := superpose eq9 eq7
  have eq42 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq22 eq7
  have eq398 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = ((X2 ◇ (X3 ◇ X2)) ◇ X3) := superpose eq24 eq7
  have eq493 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X0) = ((X3 ◇ (X4 ◇ X3)) ◇ X4) := superpose eq12 eq398
  have eq562 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) = (X4 ◇ (X3 ◇ X4)) := superpose eq398 eq7
  have eq614 (X1 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ X2) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X1))) = (X4 ◇ (X3 ◇ X4)) := superpose eq11 eq562
  have eq640 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X0) = (X3 ◇ (((X4 ◇ X4) ◇ X4) ◇ X3)) := superpose eq12 eq26
  have eq716 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X2 ◇ X2) ◇ X2) ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X4)) ◇ ((((X5 ◇ X5) ◇ X5) ◇ X6) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) = X6 := superpose eq26 eq24
  have eq720 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ X2) ◇ ((((X3 ◇ X3) ◇ X3) ◇ X4) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)))) = X4 := superpose eq26 eq7
  have eq783 (X1 X2 X3 X4 X5 X6 : G) : ((((X2 ◇ X2) ◇ X2) ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X4)) ◇ ((((X5 ◇ X5) ◇ X5) ◇ X6) ◇ ((X1 ◇ X1) ◇ X1))) = X6 := superpose eq11 eq716
  have eq787 (X1 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ X2) ◇ ((((X3 ◇ X3) ◇ X3) ◇ X4) ◇ ((X1 ◇ X1) ◇ X1))) = X4 := superpose eq11 eq720
  have eq833 (X0 X1 X3 X4 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X3 ◇ (X4 ◇ X3))) = X4 := superpose eq493 eq7
  have eq849 (X0 X1 X2 X4 : G) : (X2 ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X2 ◇ ((X4 ◇ X4) ◇ X4))) := superpose eq493 eq42
  have eq1701 (X0 X1 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) ◇ (X3 ◇ (X4 ◇ X3))) = X4 := superpose eq640 eq7
  have eq3804 (X0 X1 X2 X4 X5 : G) : ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) ◇ (X4 ◇ (X5 ◇ X4))) = X5 := superpose eq493 eq1701
  have eq4631 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose eq42 eq787
  have eq5934 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X1 ◇ X4)) := superpose eq614 eq614
  have eq5935 (X0 X3 : G) : (X0 ◇ X0) = (X3 ◇ (X0 ◇ X3)) := superpose eq42 eq614
  have eq6188 (X0 X1 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq4631 eq5935
  have eq6636 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq5935 eq5934
  have eq7107 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = (((X2 ◇ X2) ◇ X2) ◇ X0) := superpose eq6188 eq7
  have eq7149 (X0 X2 : G) : (((X2 ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq10 eq7107
  have eq7176 (X1 X2 X3 X4 X6 : G) : ((((X2 ◇ X2) ◇ X2) ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X4)) ◇ (X6 ◇ ((X1 ◇ X1) ◇ X1))) = X6 := superpose eq7149 eq783
  have eq7420 (X1 X3 X4 X6 : G) : (((X3 ◇ (X4 ◇ X3)) ◇ X4) ◇ (X6 ◇ ((X1 ◇ X1) ◇ X1))) = X6 := superpose eq7149 eq7176
  have eq7421 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq7420 eq849
  have eq7426 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq7421 eq7
  have eq7584 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq7421 eq7426
  have eq7586 (X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = X1 := superpose eq7584 eq6636
  have eq7598 (X1 X3 X4 : G) : ((X1 ◇ X1) ◇ (X3 ◇ (X4 ◇ X3))) = X4 := superpose eq7586 eq833
  have eq7602 (X1 X2 X4 X5 : G) : ((X2 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X4 ◇ (X5 ◇ X4))) = X5 := superpose eq7586 eq3804
  have eq7619 (X1 X4 : G) : ((X1 ◇ X1) ◇ X4) = X4 := superpose eq7586 eq7598
  have eq7620 (X1 X4 : G) : (X1 ◇ X4) = X4 := superpose eq7421 eq7619
  have eq7626 (X1 X2 X4 X5 : G) : ((X2 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X5 ◇ X4)) = X5 := superpose eq7620 eq7602
  have eq7627 (X1 X2 X4 X5 : G) : ((X2 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X4) = X5 := superpose eq7620 eq7626
  have eq7628 (X1 X2 X4 X5 : G) : (((X1 ◇ X1) ◇ X2) ◇ X4) = X5 := superpose eq7620 eq7627
  have eq7629 (X2 X4 X5 : G) : (X2 ◇ X4) = X5 := superpose eq7620 eq7628
  have eq7642 (X0 X1 : G) : X0 = X1 := superpose eq7421 eq7629
  have eq7656 (X0 : G) : sK0 ≠ X0 := superpose eq7642 eq8
  subsumption eq7656 eq7642


@[equational_result]
theorem Equation23526_implies_Equation2 (G : Type*) [Magma G] (h : Equation23526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation23528_implies_Equation2 (G : Type*) [Magma G] (h : Equation23528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation23529_implies_Equation2 (G : Type*) [Magma G] (h : Equation23529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23530_implies_Equation2 (G : Type*) [Magma G] (h : Equation23530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23532_implies_Equation2 (G : Type*) [Magma G] (h : Equation23532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23533_implies_Equation2 (G : Type*) [Magma G] (h : Equation23533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation23534_implies_Equation2 (G : Type*) [Magma G] (h : Equation23534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23536_implies_Equation2 (G : Type*) [Magma G] (h : Equation23536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23537_implies_Equation2 (G : Type*) [Magma G] (h : Equation23537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23538_implies_Equation2 (G : Type*) [Magma G] (h : Equation23538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23539_implies_Equation2 (G : Type*) [Magma G] (h : Equation23539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23541_implies_Equation2 (G : Type*) [Magma G] (h : Equation23541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq23 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq15 eq10
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = X2 := superpose eq15 eq23
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq44 eq33


@[equational_result]
theorem Equation23543_implies_Equation2 (G : Type*) [Magma G] (h : Equation23543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X1) = (((X2 ◇ X2) ◇ X3) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq14 eq12
  have eq22 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq14 eq10
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq22 eq21
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq22 eq26
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation23545_implies_Equation2 (G : Type*) [Magma G] (h : Equation23545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq9 eq9
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = X2 := superpose eq13 eq9
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq37 eq27


@[equational_result]
theorem Equation23547_implies_Equation2 (G : Type*) [Magma G] (h : Equation23547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X1) ◇ X4))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq14
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq65 eq38


@[equational_result]
theorem Equation23550_implies_Equation2 (G : Type*) [Magma G] (h : Equation23550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) := superpose eq10 eq10
  have eq13 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq7 eq10
  have eq16 (X0 X1 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq10 eq7
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X2 := superpose eq10 eq7
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq13
  have eq27 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))))) = X3 := superpose eq10 eq9
  have eq28 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))))) = X2 := superpose eq9 eq9
  have eq30 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) := superpose eq10 eq9
  have eq37 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) = X3 := superpose eq16 eq27
  have eq38 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) = X3 := superpose eq20 eq37
  have eq39 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X3 := superpose eq20 eq38
  have eq41 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X3 ◇ X3) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) := superpose eq39 eq30
  have eq42 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq41 eq28
  have eq52 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq42 eq42
  have eq61 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq52 eq18
  have eq66 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq52 eq41
  have eq71 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X1 := superpose eq61 eq12
  have eq95 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X0 := superpose eq42 eq71
  have eq104 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq52 eq95
  have eq108 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X3 ◇ X3) ◇ (X1 ◇ X2)) := superpose eq104 eq66
  have eq120 (X1 X3 : G) : (X1 ◇ X1) = ((X3 ◇ X3) ◇ X1) := superpose eq104 eq108
  have eq121 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X1) := superpose eq104 eq120
  have eq122 (X1 X3 : G) : (X3 ◇ X1) = X1 := superpose eq104 eq121
  have eq131 (X0 X1 : G) : X0 = X1 := superpose eq122 eq104
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq145 eq131


@[equational_result]
theorem Equation23551_implies_Equation2 (G : Type*) [Magma G] (h : Equation23551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X4))) = X3 := superpose eq7 eq7
  have eq38 (X0 X1 X2 X6 : G) : (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X6))) = X2 := superpose eq9 eq9
  have eq42 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq59 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq42 eq38
  have eq83 (X0 X2 : G) : X0 = X2 := superpose eq42 eq59
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq100 eq83


@[equational_result]
theorem Equation23553_implies_Equation2 (G : Type*) [Magma G] (h : Equation23553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq10 eq10
  have eq25 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq14 eq10
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq39 eq26


@[equational_result]
theorem Equation23554_implies_Equation2 (G : Type*) [Magma G] (h : Equation23554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq9 eq9
  have eq24 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq15 eq9
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq39 eq26


@[equational_result]
theorem Equation23555_implies_Equation2 (G : Type*) [Magma G] (h : Equation23555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X4))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq14 eq10
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation23556_implies_Equation2 (G : Type*) [Magma G] (h : Equation23556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X6))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq21 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq13 eq10
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation23558_implies_Equation2 (G : Type*) [Magma G] (h : Equation23558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq9 eq9
  have eq19 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq13 eq9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = X2 := superpose eq13 eq19
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq38 eq27


@[equational_result]
theorem Equation23559_implies_Equation2 (G : Type*) [Magma G] (h : Equation23559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = (((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2))))) ◇ X0) := superpose eq9 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))))) ◇ (X1 ◇ X0)) = X3 := superpose eq9 eq7
  have eq57 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) = (X3 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq10 eq13
  have eq64 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X3 ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X2))) := superpose eq10 eq13
  have eq85 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X2 := superpose eq13 eq7
  have eq91 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X1) = (((((((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ X3) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X4 ◇ X3)) ◇ X4) := superpose eq10 eq11
  have eq196 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq13 eq14
  have eq213 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq85 eq196
  have eq214 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq213 eq13
  have eq247 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X2)) := superpose eq214 eq57
  have eq286 (X1 X3 X4 : G) : (X1 ◇ X1) = (((((X1 ◇ X1) ◇ X3) ◇ ((X1 ◇ X1) ◇ X3)) ◇ (X4 ◇ X3)) ◇ X4) := superpose eq247 eq91
  have eq291 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq11 eq286
  have eq294 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X0)) := superpose eq291 eq10
  have eq296 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X2))))) ◇ X0) := superpose eq291 eq14
  have eq297 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))))) ◇ (X1 ◇ X0)) = X3 := superpose eq291 eq15
  have eq321 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ (((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X2))) := superpose eq291 eq64
  have eq351 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X0)) := superpose eq291 eq294
  have eq353 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0) = X2 := superpose eq291 eq296
  have eq354 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2))))) ◇ (X1 ◇ X0)) = X3 := superpose eq291 eq297
  have eq404 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X2))) := superpose eq291 eq321
  have eq405 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X1 ◇ X3)) := superpose eq351 eq404
  have eq406 (X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = X1 := superpose eq291 eq405
  have eq408 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X2 := superpose eq406 eq353
  have eq409 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X0)) = X3 := superpose eq406 eq354
  have eq415 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq406 eq408
  have eq416 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq409 eq351
  have eq461 (X0 X1 : G) : X0 = X1 := superpose eq416 eq415
  have eq474 (X0 : G) : sK0 ≠ X0 := superpose eq461 eq8
  subsumption eq474 eq461


@[equational_result]
theorem Equation23560_implies_Equation2 (G : Type*) [Magma G] (h : Equation23560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq139 eq57


@[equational_result]
theorem Equation23562_implies_Equation2 (G : Type*) [Magma G] (h : Equation23562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation23563_implies_Equation2 (G : Type*) [Magma G] (h : Equation23563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23564_implies_Equation2 (G : Type*) [Magma G] (h : Equation23564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23566_implies_Equation2 (G : Type*) [Magma G] (h : Equation23566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23567_implies_Equation2 (G : Type*) [Magma G] (h : Equation23567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23568_implies_Equation2 (G : Type*) [Magma G] (h : Equation23568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23570_implies_Equation2 (G : Type*) [Magma G] (h : Equation23570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23571_implies_Equation2 (G : Type*) [Magma G] (h : Equation23571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23572_implies_Equation2 (G : Type*) [Magma G] (h : Equation23572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23573_implies_Equation2 (G : Type*) [Magma G] (h : Equation23573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23577_implies_Equation2 (G : Type*) [Magma G] (h : Equation23577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq9 eq9
  have eq23 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq18 eq10
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq47 eq25


@[equational_result]
theorem Equation23579_implies_Equation2 (G : Type*) [Magma G] (h : Equation23579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23580_implies_Equation2 (G : Type*) [Magma G] (h : Equation23580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23581_implies_Equation2 (G : Type*) [Magma G] (h : Equation23581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23583_implies_Equation2 (G : Type*) [Magma G] (h : Equation23583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23584_implies_Equation2 (G : Type*) [Magma G] (h : Equation23584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23585_implies_Equation2 (G : Type*) [Magma G] (h : Equation23585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23587_implies_Equation2 (G : Type*) [Magma G] (h : Equation23587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23588_implies_Equation2 (G : Type*) [Magma G] (h : Equation23588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23589_implies_Equation2 (G : Type*) [Magma G] (h : Equation23589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23590_implies_Equation2 (G : Type*) [Magma G] (h : Equation23590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23592_implies_Equation2 (G : Type*) [Magma G] (h : Equation23592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X1 ◇ X1)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq10
  have eq25 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq13 eq10
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq39 eq26


@[equational_result]
theorem Equation23593_implies_Equation2 (G : Type*) [Magma G] (h : Equation23593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq52 eq19


@[equational_result]
theorem Equation23594_implies_Equation2 (G : Type*) [Magma G] (h : Equation23594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X3))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq113 eq36


@[equational_result]
theorem Equation23595_implies_Equation2 (G : Type*) [Magma G] (h : Equation23595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation23597_implies_Equation2 (G : Type*) [Magma G] (h : Equation23597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23598_implies_Equation2 (G : Type*) [Magma G] (h : Equation23598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23599_implies_Equation2 (G : Type*) [Magma G] (h : Equation23599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23600_implies_Equation2 (G : Type*) [Magma G] (h : Equation23600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23602_implies_Equation2 (G : Type*) [Magma G] (h : Equation23602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23603_implies_Equation2 (G : Type*) [Magma G] (h : Equation23603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23604_implies_Equation2 (G : Type*) [Magma G] (h : Equation23604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23605_implies_Equation2 (G : Type*) [Magma G] (h : Equation23605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23607_implies_Equation2 (G : Type*) [Magma G] (h : Equation23607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23608_implies_Equation2 (G : Type*) [Magma G] (h : Equation23608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23609_implies_Equation2 (G : Type*) [Magma G] (h : Equation23609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23610_implies_Equation2 (G : Type*) [Magma G] (h : Equation23610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23612_implies_Equation2 (G : Type*) [Magma G] (h : Equation23612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23613_implies_Equation2 (G : Type*) [Magma G] (h : Equation23613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23614_implies_Equation2 (G : Type*) [Magma G] (h : Equation23614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23615_implies_Equation2 (G : Type*) [Magma G] (h : Equation23615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23616_implies_Equation2 (G : Type*) [Magma G] (h : Equation23616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23637_implies_Equation2 (G : Type*) [Magma G] (h : Equation23637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq12
  have eq20 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X4))) = X2 := superpose eq12 eq7
  have eq48 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X1) ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq17
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq17
  have eq62 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X2))) = X2 := superpose eq48 eq20
  have eq63 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq49 eq62
  have eq100 (X0 X4 : G) : X0 = X4 := superpose eq7 eq63
  have eq215 (X0 : G) : sK0 ≠ X0 := superpose eq100 eq8
  subsumption eq215 eq100


@[equational_result]
theorem Equation23639_implies_Equation2 (G : Type*) [Magma G] (h : Equation23639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq10
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq94 eq39


@[equational_result]
theorem Equation23640_implies_Equation2 (G : Type*) [Magma G] (h : Equation23640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X2 := superpose eq7 eq10
  have eq29 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq9 eq9
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq29
  have eq37 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq36 eq7
  have eq38 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq36 eq9
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq36 eq38
  have eq73 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq10 eq36
  have eq79 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X2 ◇ X3) ◇ X0) ◇ X0)) := superpose eq36 eq10
  have eq82 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq73 eq13
  have eq87 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq73 eq79
  have eq88 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq82 eq87
  have eq90 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq88 eq37
  have eq91 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq88 eq49
  have eq97 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq88 eq90
  have eq98 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq88 eq91
  have eq99 (X0 X1 : G) : X0 = X1 := superpose eq97 eq98
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq104 eq99


@[equational_result]
theorem Equation23641_implies_Equation2 (G : Type*) [Magma G] (h : Equation23641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X5))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X1 ◇ X3)) = (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X4))) := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ X5) = ((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) ◇ (X1 ◇ (X1 ◇ X6))) := superpose eq10 eq7
  have eq65 (X0 X1 X5 X6 X7 : G) : ((X1 ◇ X0) ◇ X0) = (X5 ◇ (((X1 ◇ X0) ◇ X6) ◇ (((X1 ◇ X0) ◇ X6) ◇ X7))) := superpose eq9 eq10
  have eq71 (X1 X2 X5 X6 : G) : ((X1 ◇ X2) ◇ X5) = (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X1 ◇ X6))) := superpose eq65 eq31
  have eq74 (X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X5) = X2 := superpose eq7 eq71
  have eq75 (X0 X1 X5 X6 X7 : G) : (X5 ◇ (((X1 ◇ X0) ◇ X6) ◇ (((X1 ◇ X0) ◇ X6) ◇ X7))) = X0 := superpose eq74 eq65
  have eq104 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq74 eq75
  have eq105 (X0 X3 : G) : X0 = X3 := superpose eq104 eq104
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq117 eq105


@[equational_result]
theorem Equation23643_implies_Equation2 (G : Type*) [Magma G] (h : Equation23643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2))) = X3 := superpose eq10 eq7
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq10 eq9
  have eq52 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq36 eq36
  have eq60 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq36 eq7
  have eq67 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) = ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq36 eq10
  have eq73 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq10 eq67
  have eq81 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X4) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ X3) ◇ X1) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X1))))) = X4 := superpose eq9 eq11
  have eq115 (X0 X1 X4 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X4) ◇ (X0 ◇ X1)) = X4 := superpose eq9 eq81
  have eq178 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq115
  have eq183 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq115
  have eq197 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0)) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq115 eq7
  have eq204 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0)) = (X0 ◇ ((((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ X0)) := superpose eq115 eq36
  have eq218 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) = ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) ◇ X0) := superpose eq115 eq178
  have eq291 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0)) := superpose eq218 eq204
  have eq292 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0)) := superpose eq10 eq291
  have eq293 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq292 eq197
  have eq300 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X3 := superpose eq293 eq183
  have eq302 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq300 eq60
  have eq349 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq302 eq52
  have eq350 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq302 eq73
  have eq363 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq302 eq350
  have eq365 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := superpose eq363 eq10
  have eq367 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq363 eq17
  have eq436 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq363 eq365
  have eq437 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq436 eq349
  have eq440 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq300 eq437
  have eq460 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X2) = X3 := superpose eq440 eq367
  have eq461 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = X3 := superpose eq440 eq460
  have eq462 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq440 eq461
  have eq463 (X0 X3 : G) : X0 = X3 := superpose eq462 eq462
  have eq468 (X0 : G) : sK0 ≠ X0 := superpose eq463 eq8
  subsumption eq468 eq463


@[equational_result]
theorem Equation23645_implies_Equation2 (G : Type*) [Magma G] (h : Equation23645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X5))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X5) ◇ X4) = X5 := superpose eq7 eq12
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = (X0 ◇ X2) := superpose eq7 eq12
  have eq19 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X0 ◇ X4))) = X3 := superpose eq12 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (((((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X1) ◇ X0) ◇ X3) ◇ X5) ◇ X0) = X5 := superpose eq12 eq7
  have eq23 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X5) ◇ X4) = X5 := superpose eq18 eq13
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq18 eq9
  have eq26 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ (X1 ◇ X1)) = X4 := superpose eq18 eq25
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = X3 := superpose eq18 eq19
  have eq29 (X0 X1 X3 X5 : G) : (((X1 ◇ X3) ◇ X5) ◇ X0) = X5 := superpose eq23 eq22
  have eq33 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq29 eq27
  have eq34 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ X1) = X4 := superpose eq33 eq26
  have eq43 (X1 X4 : G) : (X4 ◇ X1) = X4 := superpose eq33 eq34
  have eq52 (X0 X1 : G) : X0 = X1 := superpose eq43 eq33
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq62 eq52


@[equational_result]
theorem Equation23647_implies_Equation2 (G : Type*) [Magma G] (h : Equation23647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X3 := superpose eq7 eq12
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq12 eq12
  have eq23 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq16 eq12
  have eq24 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X4 := superpose eq23 eq11
  have eq28 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X0)) = X4 := superpose eq18 eq24
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq28 eq28
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq35 eq33


@[equational_result]
theorem Equation23648_implies_Equation2 (G : Type*) [Magma G] (h : Equation23648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X3 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5) ◇ (X1 ◇ X0)) = X5 := superpose eq7 eq7
  have eq60 (X0 X1 X2 X6 : G) : (X0 ◇ (X1 ◇ X2)) = X6 := superpose eq10 eq11
  have eq78 (X0 X4 : G) : X0 = X4 := superpose eq7 eq60
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq170 eq78


@[equational_result]
theorem Equation23649_implies_Equation2 (G : Type*) [Magma G] (h : Equation23649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X3 ◇ X3)) = (X0 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X4))) := superpose eq7 eq7
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq10
  have eq112 (X0 X3 : G) : X0 = X3 := superpose eq7 eq39
  have eq144 (X0 : G) : sK0 ≠ X0 := superpose eq112 eq8
  subsumption eq144 eq112


@[equational_result]
theorem Equation23650_implies_Equation2 (G : Type*) [Magma G] (h : Equation23650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq23 (X0 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ X5) = X7 := superpose eq7 eq12
  have eq28 (X0 X3 X5 X6 : G) : (((X0 ◇ X5) ◇ X6) ◇ X3) = X6 := superpose eq12 eq12
  have eq43 (X5 X6 X7 : G) : (X6 ◇ X5) = X7 := superpose eq28 eq23
  have eq46 (X0 X5 : G) : X0 = X5 := superpose eq7 eq43
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq83 eq46


@[equational_result]
theorem Equation23654_implies_Equation2 (G : Type*) [Magma G] (h : Equation23654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ X4) = X0 := superpose eq12 eq12
  have eq18 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq12 eq12
  have eq24 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq18 eq16
  have eq34 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq24 eq18
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq50 eq36


@[equational_result]
theorem Equation23657_implies_Equation2 (G : Type*) [Magma G] (h : Equation23657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ (X4 ◇ X3)) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq10
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq10
  have eq37 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (X3 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X4) ◇ (X0 ◇ (X1 ◇ X0))) = X4 := superpose eq9 eq10
  have eq59 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X4 ◇ (X5 ◇ X4))) ◇ X6) ◇ X0) = X6 := superpose eq13 eq13
  have eq70 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq7 eq15
  have eq99 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X2)) ◇ X4) ◇ (X0 ◇ (X1 ◇ X0))) = X4 := superpose eq70 eq37
  have eq100 (X0 X3 X6 : G) : ((X3 ◇ X6) ◇ X0) = X6 := superpose eq99 eq59
  have eq101 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X2))) = X0 := superpose eq100 eq7
  have eq147 (X1 X2 : G) : (X1 ◇ X2) = (X2 ◇ (X1 ◇ X2)) := superpose eq100 eq70
  have eq155 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X2)) = X0 := superpose eq147 eq101
  have eq165 (X0 X3 : G) : X0 = X3 := superpose eq155 eq155
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq165 eq8
  subsumption eq168 eq165


@[equational_result]
theorem Equation23658_implies_Equation2 (G : Type*) [Magma G] (h : Equation23658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ X3) = X4 := superpose eq12 eq12
  have eq62 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq16 eq16
  have eq86 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq62 eq16
  have eq125 (X0 X3 : G) : X0 = X3 := superpose eq86 eq86
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq125 eq8
  subsumption eq127 eq125


@[equational_result]
theorem Equation23661_implies_Equation2 (G : Type*) [Magma G] (h : Equation23661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq10 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))))) = X2 := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X2 := superpose eq9 eq9
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq9
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X2 := superpose eq25 eq23
  have eq43 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq27 eq7
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) := superpose eq27 eq7
  have eq60 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X2 := superpose eq43 eq34
  have eq61 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq43 eq25
  have eq62 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq43 eq60
  have eq71 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq62 eq61
  have eq73 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X2))) = X2 := superpose eq71 eq18
  have eq82 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq73 eq50
  have eq83 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = X0 := superpose eq82 eq7
  have eq104 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq82 eq83
  have eq105 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq82 eq104
  have eq136 (X0 X1 : G) : X0 = X1 := superpose eq105 eq82
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq136 eq8
  subsumption eq150 eq136


@[equational_result]
theorem Equation23662_implies_Equation2 (G : Type*) [Magma G] (h : Equation23662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X5))) = X4 := superpose eq7 eq7
  have eq40 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X5))) = X3 := superpose eq9 eq9
  have eq47 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9
  have eq65 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X3 := superpose eq47 eq40
  have eq73 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = X0 := superpose eq65 eq7
  have eq102 (X0 X3 : G) : X0 = X3 := superpose eq73 eq73
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq121 eq102


@[equational_result]
theorem Equation23664_implies_Equation2 (G : Type*) [Magma G] (h : Equation23664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X1)) = (X0 ◇ (X0 ◇ (X4 ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X4)) = (X5 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq10 eq10
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X4 := superpose eq10 eq7
  have eq32 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X5) ◇ ((X4 ◇ X2) ◇ (X6 ◇ X3))) = X5 := superpose eq10 eq7
  have eq148 (X0 X1 X3 X4 : G) : ((X0 ◇ X4) ◇ (X3 ◇ X1)) = X4 := superpose eq7 eq12
  have eq185 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X5) ◇ X2) = X5 := superpose eq148 eq32
  have eq186 (X0 X1 X2 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq148 eq27
  have eq201 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq186 eq30
  have eq204 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq186 eq185
  have eq234 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq204 eq201
  have eq237 (X0 X3 : G) : X0 = X3 := superpose eq234 eq234
  have eq261 (X0 : G) : sK0 ≠ X0 := superpose eq237 eq8
  subsumption eq261 eq237


@[equational_result]
theorem Equation23665_implies_Equation2 (G : Type*) [Magma G] (h : Equation23665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq37 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X0) = X4 := superpose eq12 eq12
  have eq39 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq12 eq12
  have eq51 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq39 eq37
  have eq68 (X0 X2 : G) : X0 = X2 := superpose eq51 eq51
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq92 eq68


@[equational_result]
theorem Equation23666_implies_Equation2 (G : Type*) [Magma G] (h : Equation23666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X3)) = (X0 ◇ (X0 ◇ (X4 ◇ X4))) := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ (X3 ◇ (X4 ◇ X4))) = X0 := superpose eq7 eq10
  have eq71 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq124 eq71


@[equational_result]
theorem Equation23667_implies_Equation2 (G : Type*) [Magma G] (h : Equation23667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq112 (X0 X1 X5 X6 : G) : (((X1 ◇ X0) ◇ X6) ◇ X5) = X6 := superpose eq12 eq12
  have eq114 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq11 eq12
  have eq152 (X0 X5 X6 : G) : (X0 ◇ X5) = X6 := superpose eq114 eq112
  have eq160 (X0 X3 : G) : X0 = X3 := superpose eq152 eq152
  have eq201 (X0 : G) : sK0 ≠ X0 := superpose eq160 eq8
  subsumption eq201 eq160


@[equational_result]
theorem Equation23669_implies_Equation2 (G : Type*) [Magma G] (h : Equation23669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X0 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := superpose eq7 eq12
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq12 eq12
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq18 eq17
  have eq30 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq29 eq12
  have eq35 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = X3 := superpose eq29 eq30
  have eq36 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq29 eq35
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq36 eq36
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation23670_implies_Equation2 (G : Type*) [Magma G] (h : Equation23670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ ((X2 ◇ X3) ◇ X0)) = X5 := superpose eq7 eq12
  have eq15 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq7 eq12
  have eq24 (X0 X2 X3 X5 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X0)) = X5 := superpose eq15 eq13
  have eq28 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq15 eq24
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq81 eq39


@[equational_result]
theorem Equation23671_implies_Equation2 (G : Type*) [Magma G] (h : Equation23671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ X0) = (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ ((X5 ◇ (X0 ◇ X5)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq9 eq9
  have eq18 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq26 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq12
  have eq42 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq18 eq18
  have eq43 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq18 eq7
  have eq51 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq43 eq26
  have eq55 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq51 eq11
  have eq57 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq51 eq16
  have eq61 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = (((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X0) := superpose eq42 eq55
  have eq63 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq42 eq57
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ X2) := superpose eq12 eq61
  have eq84 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq18 eq77
  have eq87 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq84 eq63
  have eq93 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq87 eq51
  have eq97 (X0 X1 : G) : X0 = X1 := superpose eq87 eq93
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq102 eq97


@[equational_result]
theorem Equation23672_implies_Equation2 (G : Type*) [Magma G] (h : Equation23672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation23674_implies_Equation2 (G : Type*) [Magma G] (h : Equation23674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq12 eq12
  have eq24 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq12
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq39 eq26


@[equational_result]
theorem Equation23675_implies_Equation2 (G : Type*) [Magma G] (h : Equation23675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq10 eq10
  have eq22 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq11
  have eq33 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq22 eq15
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq10 eq33
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq55 eq37


@[equational_result]
theorem Equation23676_implies_Equation2 (G : Type*) [Magma G] (h : Equation23676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X3)) = (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X4))) := superpose eq7 eq7
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq10
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq169 eq73


@[equational_result]
theorem Equation23677_implies_Equation2 (G : Type*) [Magma G] (h : Equation23677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq15 eq12
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation23679_implies_Equation2 (G : Type*) [Magma G] (h : Equation23679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 X6 : G) : (((X0 ◇ X4) ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq23 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq13 eq12
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation23680_implies_Equation2 (G : Type*) [Magma G] (h : Equation23680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq12 eq12
  have eq15 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq12
  have eq23 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq15 eq14
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq65 eq38


@[equational_result]
theorem Equation23681_implies_Equation2 (G : Type*) [Magma G] (h : Equation23681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ (X2 ◇ X3)) = (X0 ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq7 eq7
  have eq44 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X2) := superpose eq10 eq9
  have eq67 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq9 eq44
  have eq164 (X0 X4 : G) : X0 = X4 := superpose eq7 eq67
  have eq299 (X0 : G) : sK0 ≠ X0 := superpose eq164 eq8
  subsumption eq299 eq164


@[equational_result]
theorem Equation23682_implies_Equation2 (G : Type*) [Magma G] (h : Equation23682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation23684_implies_Equation2 (G : Type*) [Magma G] (h : Equation23684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ (X5 ◇ ((X1 ◇ X2) ◇ X0)))) = X4 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ X1))) = X0 := superpose eq21 eq7
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq29 eq29
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation23685_implies_Equation2 (G : Type*) [Magma G] (h : Equation23685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X2)) = (X0 ◇ (X4 ◇ (X4 ◇ X0))) := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ (X4 ◇ X3))) = X0 := superpose eq7 eq10
  have eq111 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq111 eq8
  subsumption eq140 eq111


@[equational_result]
theorem Equation23686_implies_Equation2 (G : Type*) [Magma G] (h : Equation23686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X3 ◇ (X3 ◇ X3)) = (X0 ◇ (X4 ◇ (X4 ◇ X4))) := superpose eq7 eq7
  have eq27 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq10
  have eq47 (X0 X2 : G) : X0 = X2 := superpose eq27 eq27
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq110 eq47


@[equational_result]
theorem Equation23687_implies_Equation2 (G : Type*) [Magma G] (h : Equation23687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq22 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation23689_implies_Equation2 (G : Type*) [Magma G] (h : Equation23689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ X6) ◇ X7) = X6 := superpose eq7 eq12
  have eq23 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq13 eq12
  have eq25 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation23690_implies_Equation2 (G : Type*) [Magma G] (h : Equation23690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq12
  have eq15 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq23 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq15 eq13
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq86 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq86 eq39


@[equational_result]
theorem Equation23691_implies_Equation2 (G : Type*) [Magma G] (h : Equation23691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation23692_implies_Equation2 (G : Type*) [Magma G] (h : Equation23692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation23693_implies_Equation2 (G : Type*) [Magma G] (h : Equation23693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation23695_implies_Equation2 (G : Type*) [Magma G] (h : Equation23695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X3) ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X2 := superpose eq10 eq7
  have eq23 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = ((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq9 eq9
  have eq24 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1)))))) = X3 := superpose eq9 eq7
  have eq26 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq9 eq10
  have eq119 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X0 := superpose eq17 eq12
  have eq121 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = ((((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq12 eq11
  have eq132 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq119 eq121
  have eq134 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq132 eq12
  have eq135 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq134 eq23
  have eq136 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq134 eq135
  have eq138 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq136 eq26
  have eq140 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq134 eq138
  have eq147 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))))) = X3 := superpose eq140 eq24
  have eq161 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1)))) = X3 := superpose eq140 eq147
  have eq162 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1))) = X3 := superpose eq140 eq161
  have eq163 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = X3 := superpose eq140 eq162
  have eq187 (X0 X4 : G) : X0 = X4 := superpose eq163 eq163
  have eq291 (X0 : G) : sK0 ≠ X0 := superpose eq187 eq8
  subsumption eq291 eq187


@[equational_result]
theorem Equation23697_implies_Equation2 (G : Type*) [Magma G] (h : Equation23697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq14 eq12
  have eq22 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq14 eq10
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq22 eq21
  have eq29 (X0 X1 : G) : X0 = X1 := superpose eq22 eq27
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation23699_implies_Equation2 (G : Type*) [Magma G] (h : Equation23699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq10 eq7
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq11 eq11
  have eq20 (X0 X1 X3 : G) : (((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq11 eq7
  have eq23 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ ((((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq11 eq10
  have eq25 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq11 eq10
  have eq37 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq13 eq11
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq13 eq37
  have eq45 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq44 eq25
  have eq46 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq44 eq12
  have eq47 (X0 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := superpose eq44 eq23
  have eq55 (X0 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq44 eq20
  have eq58 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) := superpose eq46 eq47
  have eq91 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq7 eq19
  have eq98 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq19
  have eq133 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq98 eq45
  have eq134 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X2) := superpose eq133 eq58
  have eq139 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X0))) = X3 := superpose eq134 eq55
  have eq141 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq139 eq133
  have eq143 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq141 eq13
  have eq147 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq141 eq44
  have eq165 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ X3) ◇ X1) := superpose eq147 eq91
  have eq169 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq147 eq165
  have eq170 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq169 eq143
  have eq174 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq169 eq170
  have eq202 (X0 X2 : G) : X0 = X2 := superpose eq174 eq174
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq202 eq8
  subsumption eq207 eq202


@[equational_result]
theorem Equation23700_implies_Equation2 (G : Type*) [Magma G] (h : Equation23700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) = X3 := superpose eq7 eq9
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2))) := superpose eq9 eq10
  have eq39 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) = (((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq7
  have eq40 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X4 ◇ ((((X2 ◇ X3) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ X2)))) = X4 := superpose eq10 eq9
  have eq54 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X6 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X4))))) = X6 := superpose eq11 eq11
  have eq82 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq13
  have eq99 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X4 ◇ ((X2 ◇ X3) ◇ X2))) = X4 := superpose eq82 eq40
  have eq100 (X0 X3 X6 : G) : (X0 ◇ (X6 ◇ X3)) = X6 := superpose eq99 eq54
  have eq101 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq100 eq39
  have eq111 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq100 eq25
  have eq157 (X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X1) = X2 := superpose eq111 eq101
  have eq160 (X1 X2 X3 : G) : (X3 ◇ X1) = X2 := superpose eq111 eq157
  have eq161 (X0 X3 : G) : X0 = X3 := superpose eq160 eq160
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq161 eq8
  subsumption eq169 eq161


@[equational_result]
theorem Equation23701_implies_Equation2 (G : Type*) [Magma G] (h : Equation23701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = X0 := superpose eq17 eq7
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq39 eq36


@[equational_result]
theorem Equation23703_implies_Equation2 (G : Type*) [Magma G] (h : Equation23703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X1)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq7 eq11
  have eq51 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = ((X3 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))))) := superpose eq12 eq12
  have eq69 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))))) = X3 := superpose eq12 eq7
  have eq76 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = ((X3 ◇ X2) ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))))) := superpose eq7 eq51
  have eq85 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))))) = X3 := superpose eq7 eq69
  have eq115 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq10
  have eq118 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq10 eq9
  have eq125 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X2) ◇ X3)) ◇ (X1 ◇ (X2 ◇ X3))) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose eq10 eq12
  have eq126 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ X2) ◇ X3)) ◇ (X1 ◇ (X2 ◇ X3))) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X4 := superpose eq10 eq9
  have eq146 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq12 eq118
  have eq152 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X1 ◇ X0) ◇ X0) := superpose eq10 eq125
  have eq153 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ (X4 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X4 := superpose eq10 eq126
  have eq157 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (((X0 ◇ X1) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq11 eq115
  have eq187 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq157
  have eq224 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1))) ◇ (X1 ◇ X2)))) = X3 := superpose eq153 eq7
  have eq234 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X2 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2)))) ◇ X0) := superpose eq153 eq115
  have eq257 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq12 eq152
  have eq258 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq153 eq152
  have eq311 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X2 ◇ X1)) = ((((X2 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) := superpose eq258 eq234
  have eq312 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq11 eq311
  have eq315 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X2 ◇ X1) ◇ X2))) = X3 := superpose eq312 eq224
  have eq324 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = ((X3 ◇ X2) ◇ (X3 ◇ X2)) := superpose eq315 eq76
  have eq325 (X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = X3 := superpose eq315 eq85
  have eq334 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq325 eq187
  have eq347 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq334 eq146
  have eq351 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq347 eq257
  have eq353 (X2 X3 : G) : ((X3 ◇ X2) ◇ (X3 ◇ X2)) = X2 := superpose eq351 eq324
  have eq354 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq353 eq334
  have eq356 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq354 eq7
  have eq477 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq354 eq356
  have eq478 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq354 eq477
  have eq486 (X0 X2 : G) : X0 = X2 := superpose eq478 eq478
  have eq488 (X0 : G) : sK0 ≠ X0 := superpose eq486 eq8
  subsumption eq488 eq486


@[equational_result]
theorem Equation23705_implies_Equation2 (G : Type*) [Magma G] (h : Equation23705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq44 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X3 ◇ X4) := superpose eq11 eq10
  have eq68 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq44
  have eq165 (X0 X4 : G) : X0 = X4 := superpose eq7 eq68
  have eq300 (X0 : G) : sK0 ≠ X0 := superpose eq165 eq8
  subsumption eq300 eq165


@[equational_result]
theorem Equation23707_implies_Equation2 (G : Type*) [Magma G] (h : Equation23707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X4 ◇ (X5 ◇ ((X1 ◇ X2) ◇ X1)))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X1))) = X2 := superpose eq16 eq10
  have eq25 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X5) = X4 := superpose eq23 eq9
  have eq27 (X0 X2 X4 X5 : G) : ((X0 ◇ X2) ◇ X5) = X4 := superpose eq19 eq25
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq27 eq27
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq36 eq34


@[equational_result]
theorem Equation23708_implies_Equation2 (G : Type*) [Magma G] (h : Equation23708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X3) ◇ X4) = (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq7 eq11
  have eq74 (X0 X3 : G) : X0 = X3 := superpose eq40 eq40
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq169 eq74


@[equational_result]
theorem Equation23709_implies_Equation2 (G : Type*) [Magma G] (h : Equation23709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X3))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq14 eq10
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation23710_implies_Equation2 (G : Type*) [Magma G] (h : Equation23710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X5))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq21 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq13 eq10
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation23712_implies_Equation2 (G : Type*) [Magma G] (h : Equation23712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1))))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)) = X2 := superpose eq10 eq10
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X3 ◇ X1))) = X3 := superpose eq10 eq7
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq19 eq19
  have eq58 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X2 := superpose eq40 eq17
  have eq60 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X2 := superpose eq58 eq10
  have eq63 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq40 eq60
  have eq64 (X0 X3 : G) : X0 = X3 := superpose eq7 eq63
  have eq97 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq97 eq64


@[equational_result]
theorem Equation23714_implies_Equation2 (G : Type*) [Magma G] (h : Equation23714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq136 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq136 eq8
  subsumption eq157 eq136


@[equational_result]
theorem Equation23716_implies_Equation2 (G : Type*) [Magma G] (h : Equation23716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23717_implies_Equation2 (G : Type*) [Magma G] (h : Equation23717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation23718_implies_Equation2 (G : Type*) [Magma G] (h : Equation23718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23720_implies_Equation2 (G : Type*) [Magma G] (h : Equation23720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23721_implies_Equation2 (G : Type*) [Magma G] (h : Equation23721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23722_implies_Equation2 (G : Type*) [Magma G] (h : Equation23722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23724_implies_Equation2 (G : Type*) [Magma G] (h : Equation23724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23725_implies_Equation2 (G : Type*) [Magma G] (h : Equation23725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23726_implies_Equation2 (G : Type*) [Magma G] (h : Equation23726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23727_implies_Equation2 (G : Type*) [Magma G] (h : Equation23727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23731_implies_Equation2 (G : Type*) [Magma G] (h : Equation23731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq25 (X0 X1 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X0) = X3 := superpose eq17 eq12
  have eq30 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq17 eq25
  have eq31 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X4 := superpose eq30 eq14
  have eq34 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq30 eq31
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq40 eq35


@[equational_result]
theorem Equation23733_implies_Equation2 (G : Type*) [Magma G] (h : Equation23733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23734_implies_Equation2 (G : Type*) [Magma G] (h : Equation23734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation23735_implies_Equation2 (G : Type*) [Magma G] (h : Equation23735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23737_implies_Equation2 (G : Type*) [Magma G] (h : Equation23737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23738_implies_Equation2 (G : Type*) [Magma G] (h : Equation23738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23739_implies_Equation2 (G : Type*) [Magma G] (h : Equation23739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23741_implies_Equation2 (G : Type*) [Magma G] (h : Equation23741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23742_implies_Equation2 (G : Type*) [Magma G] (h : Equation23742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23743_implies_Equation2 (G : Type*) [Magma G] (h : Equation23743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23744_implies_Equation2 (G : Type*) [Magma G] (h : Equation23744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23746_implies_Equation2 (G : Type*) [Magma G] (h : Equation23746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1))))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1)))) = X4 := superpose eq7 eq10
  have eq24 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq15 eq10
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation23747_implies_Equation2 (G : Type*) [Magma G] (h : Equation23747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq60 eq19


@[equational_result]
theorem Equation23748_implies_Equation2 (G : Type*) [Magma G] (h : Equation23748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq10
  have eq24 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq15 eq10
  have eq27 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X1) = X0 := superpose eq24 eq12
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq24 eq27
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq36 eq31


@[equational_result]
theorem Equation23749_implies_Equation2 (G : Type*) [Magma G] (h : Equation23749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = X5 := superpose eq7 eq7
  have eq29 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq49 eq29


@[equational_result]
theorem Equation23751_implies_Equation2 (G : Type*) [Magma G] (h : Equation23751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23752_implies_Equation2 (G : Type*) [Magma G] (h : Equation23752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation23753_implies_Equation2 (G : Type*) [Magma G] (h : Equation23753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23754_implies_Equation2 (G : Type*) [Magma G] (h : Equation23754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23756_implies_Equation2 (G : Type*) [Magma G] (h : Equation23756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23757_implies_Equation2 (G : Type*) [Magma G] (h : Equation23757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23758_implies_Equation2 (G : Type*) [Magma G] (h : Equation23758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23759_implies_Equation2 (G : Type*) [Magma G] (h : Equation23759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23761_implies_Equation2 (G : Type*) [Magma G] (h : Equation23761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23762_implies_Equation2 (G : Type*) [Magma G] (h : Equation23762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23763_implies_Equation2 (G : Type*) [Magma G] (h : Equation23763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23764_implies_Equation2 (G : Type*) [Magma G] (h : Equation23764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23766_implies_Equation2 (G : Type*) [Magma G] (h : Equation23766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23767_implies_Equation2 (G : Type*) [Magma G] (h : Equation23767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23768_implies_Equation2 (G : Type*) [Magma G] (h : Equation23768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23769_implies_Equation2 (G : Type*) [Magma G] (h : Equation23769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23770_implies_Equation2 (G : Type*) [Magma G] (h : Equation23770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23773_implies_Equation2 (G : Type*) [Magma G] (h : Equation23773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (((X3 ◇ X2) ◇ X2) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))))) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ (X3 ◇ (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)))) = X3 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1)))) = X2 := superpose eq7 eq9
  have eq18 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X2 ◇ X1) ◇ X1) ◇ X0)) := superpose eq7 eq9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq9 eq7
  have eq29 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = (((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq10
  have eq34 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X2) = (((X3 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) ◇ X0) := superpose eq7 eq10
  have eq40 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = (((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq11 eq29
  have eq47 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (((X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq9 eq18
  have eq48 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq18
  have eq55 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X3 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X1))) = (((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X3) ◇ (X3 ◇ (X3 ◇ X1))))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq10 eq18
  have eq64 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1)))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq20 eq47
  have eq66 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq64 eq20
  have eq72 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X3 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq11 eq11
  have eq80 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)))) := superpose eq11 eq18
  have eq88 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)))) := superpose eq11 eq80
  have eq89 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)))) := superpose eq11 eq88
  have eq98 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq18 eq16
  have eq102 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq16 eq16
  have eq106 (X0 X1 X2 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) = (((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X2 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq16 eq18
  have eq121 (X0 X1 X2 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) = (((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq72 eq106
  have eq142 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq12 eq9
  have eq162 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq142
  have eq163 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq162 eq121
  have eq165 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq162 eq102
  have eq168 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq165 eq163
  have eq172 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq165 eq168
  have eq173 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)))) := superpose eq172 eq89
  have eq175 (X0 X1 X3 : G) : (((X3 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq172 eq40
  have eq176 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq172 eq11
  have eq180 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)))) := superpose eq172 eq173
  have eq183 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := superpose eq172 eq175
  have eq185 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq183 eq180
  have eq187 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq183 eq98
  have eq190 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq165 eq185
  have eq191 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq48 eq190
  have eq192 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1)))) = X2 := superpose eq191 eq16
  have eq201 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq191 eq172
  have eq204 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq201 eq64
  have eq205 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq204 eq66
  have eq208 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq191 eq187
  have eq209 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq191 eq176
  have eq276 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq209 eq7
  have eq288 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq209 eq276
  have eq289 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose eq201 eq288
  have eq340 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) := superpose eq18 eq289
  have eq342 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq7 eq289
  have eq352 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq289 eq7
  have eq363 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq289 eq18
  have eq370 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq342 eq205
  have eq376 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((X2 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq191 eq352
  have eq377 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((X2 ◇ X1) ◇ X1) := superpose eq376 eq48
  have eq388 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq363 eq208
  have eq406 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq370 eq9
  have eq420 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq370 eq406
  have eq486 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq14
  have eq558 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X4 ◇ (X4 ◇ (((X0 ◇ X1) ◇ X1) ◇ X3)))) = X4 := superpose eq10 eq486
  have eq560 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq486
  have eq578 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((((X3 ◇ X4) ◇ X4) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) := superpose eq486 eq486
  have eq580 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) := superpose eq486 eq192
  have eq582 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) := superpose eq486 eq370
  have eq586 (X0 X1 X2 X3 : G) : ((X3 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X3 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) := superpose eq486 eq18
  have eq618 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) := superpose eq201 eq586
  have eq619 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) := superpose eq580 eq618
  have eq620 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) := superpose eq582 eq619
  have eq621 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) := superpose eq582 eq620
  have eq623 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((((X3 ◇ X4) ◇ X4) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) := superpose eq621 eq578
  have eq624 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) := superpose eq623 eq340
  have eq625 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X3 ◇ (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)))) = X3 := superpose eq624 eq14
  have eq667 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq625
  have eq716 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := superpose eq667 eq388
  have eq718 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X1 := superpose eq716 eq377
  have eq722 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X2 ◇ X0)) = X2 := superpose eq718 eq10
  have eq726 (X0 X2 X3 : G) : (((X3 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2))) ◇ X0) = X2 := superpose eq718 eq34
  have eq730 (X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X3 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X1))) = (((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ (X3 ◇ (X3 ◇ X1))))) ◇ X1) := superpose eq718 eq55
  have eq745 (X1 X3 X4 : G) : (X1 ◇ (X4 ◇ (X4 ◇ (X1 ◇ X3)))) = X4 := superpose eq718 eq558
  have eq792 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := superpose eq718 eq722
  have eq798 (X0 X2 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0) = X2 := superpose eq718 eq726
  have eq802 (X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = (((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ ((X1 ◇ X3) ◇ (X3 ◇ (X3 ◇ X1))))) ◇ X1) := superpose eq718 eq730
  have eq813 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq745 eq420
  have eq814 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq745 eq813
  have eq816 (X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = ((X1 ◇ X3) ◇ X1) := superpose eq814 eq802
  have eq830 (X0 X2 : G) : (((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ X0) = X2 := superpose eq816 eq798
  have eq831 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq667 eq830
  have eq832 (X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = X3 := superpose eq831 eq816
  have eq834 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq832 eq560
  have eq837 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq832 eq792
  have eq845 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq832 eq834
  have eq849 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq845 eq837
  have eq861 (X0 X2 : G) : X0 = X2 := superpose eq849 eq849
  have eq869 (X0 : G) : sK0 ≠ X0 := superpose eq861 eq8
  subsumption eq869 eq861


@[equational_result]
theorem Equation23774_implies_Equation2 (G : Type*) [Magma G] (h : Equation23774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq23 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq15 eq10
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq23 eq15
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq34 eq29


@[equational_result]
theorem Equation23777_implies_Equation2 (G : Type*) [Magma G] (h : Equation23777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq29 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq10 eq10
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq7 eq29
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq36 eq7
  have eq38 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq36 eq10
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq36 eq38
  have eq74 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq36
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X1)) := superpose eq36 eq9
  have eq83 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq74 eq9
  have eq86 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq74 eq77
  have eq87 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq83 eq86
  have eq89 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq87 eq37
  have eq90 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq87 eq49
  have eq96 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq87 eq89
  have eq97 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq87 eq90
  have eq100 (X0 X1 : G) : X0 = X1 := superpose eq96 eq97
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq100 eq8
  subsumption eq105 eq100


@[equational_result]
theorem Equation23778_implies_Equation2 (G : Type*) [Magma G] (h : Equation23778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq38 (X0 X1 X2 X3 X4 X5 X6 : G) : (X2 ◇ (X3 ◇ (((X4 ◇ X5) ◇ (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ X6))) = X3 := superpose eq12 eq10
  have eq44 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) = X3 := superpose eq12 eq10
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq55 (X2 X3 X6 : G) : (X2 ◇ (X3 ◇ (X2 ◇ X6))) = X3 := superpose eq44 eq38
  have eq67 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq45 eq55
  have eq80 (X0 X2 : G) : X0 = X2 := superpose eq67 eq67
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq121 eq80


@[equational_result]
theorem Equation23781_implies_Equation2 (G : Type*) [Magma G] (h : Equation23781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq10 eq10
  have eq25 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X1)) = (((X2 ◇ X1) ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq10 eq7
  have eq27 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X3 := superpose eq10 eq7
  have eq34 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq9 eq9
  have eq43 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X2))) = ((X3 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq7 eq21
  have eq85 (X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X1)) = (((X2 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq43 eq25
  have eq93 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ (X1 ◇ X1)) := superpose eq27 eq85
  have eq96 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := superpose eq93 eq34
  have eq120 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) = X2 := superpose eq93 eq96
  have eq121 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq93 eq120
  have eq122 (X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq93 eq121
  have eq123 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X2 := superpose eq93 eq122
  have eq227 (X0 X2 : G) : X0 = X2 := superpose eq123 eq123
  have eq237 (X0 : G) : sK0 ≠ X0 := superpose eq227 eq8
  subsumption eq237 eq227


@[equational_result]
theorem Equation23782_implies_Equation2 (G : Type*) [Magma G] (h : Equation23782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq119 (X0 X1 X2 X4 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X4 ◇ X5)) = X4 := superpose eq10 eq10
  have eq120 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X4)) = X3 := superpose eq10 eq10
  have eq156 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq120 eq119
  have eq167 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X2) = X0 := superpose eq156 eq7
  have eq222 (X0 X3 : G) : X0 = X3 := superpose eq167 eq167
  have eq251 (X0 : G) : sK0 ≠ X0 := superpose eq222 eq8
  subsumption eq251 eq222


@[equational_result]
theorem Equation23784_implies_Equation2 (G : Type*) [Magma G] (h : Equation23784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = X0 := superpose eq17 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq29 eq29
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq38 eq36


@[equational_result]
theorem Equation23785_implies_Equation2 (G : Type*) [Magma G] (h : Equation23785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X3) ◇ X3) = (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq7 eq11
  have eq75 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq148 eq75


@[equational_result]
theorem Equation23786_implies_Equation2 (G : Type*) [Magma G] (h : Equation23786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X4 ◇ X4))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X3) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X1)))) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X3) ◇ X0) = X4 := superpose eq10 eq11
  have eq32 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq52 eq32


@[equational_result]
theorem Equation23787_implies_Equation2 (G : Type*) [Magma G] (h : Equation23787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X6))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq22 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq14 eq10
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation23791_implies_Equation2 (G : Type*) [Magma G] (h : Equation23791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ X0) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq45 eq20


@[equational_result]
theorem Equation23793_implies_Equation2 (G : Type*) [Magma G] (h : Equation23793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23794_implies_Equation2 (G : Type*) [Magma G] (h : Equation23794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation23795_implies_Equation2 (G : Type*) [Magma G] (h : Equation23795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23797_implies_Equation2 (G : Type*) [Magma G] (h : Equation23797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23798_implies_Equation2 (G : Type*) [Magma G] (h : Equation23798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23799_implies_Equation2 (G : Type*) [Magma G] (h : Equation23799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23801_implies_Equation2 (G : Type*) [Magma G] (h : Equation23801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23802_implies_Equation2 (G : Type*) [Magma G] (h : Equation23802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23803_implies_Equation2 (G : Type*) [Magma G] (h : Equation23803 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation23804_implies_Equation2 (G : Type*) [Magma G] (h : Equation23804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation23807_implies_Equation2 (G : Type*) [Magma G] (h : Equation23807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) = X0 := superpose eq11 eq11
  have eq14 (X0 X1 X3 : G) : (X3 ◇ X0) = (((X1 ◇ (X0 ◇ (X3 ◇ X0))) ◇ (X0 ◇ (X3 ◇ X0))) ◇ X0) := superpose eq11 eq11
  have eq15 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq11 eq7
  have eq31 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq7 eq12
  have eq39 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq12 eq7
  have eq42 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = ((X3 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq39 eq15
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = (((X3 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq12 eq10
  have eq75 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) = X0 := superpose eq7 eq56
  have eq77 (X0 X3 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ X0) := superpose eq75 eq14
  have eq88 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq75 eq42
  have eq121 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq77 eq88
  have eq122 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq121 eq31
  have eq140 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq121 eq122
  have eq141 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq140 eq75
  have eq145 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq140 eq141
  have eq146 (X0 X3 : G) : X0 = X3 := superpose eq145 eq145
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq146 eq8
  subsumption eq151 eq146


@[equational_result]
theorem Equation23808_implies_Equation2 (G : Type*) [Magma G] (h : Equation23808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq84 eq45


@[equational_result]
theorem Equation23810_implies_Equation2 (G : Type*) [Magma G] (h : Equation23810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation23811_implies_Equation2 (G : Type*) [Magma G] (h : Equation23811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation23812_implies_Equation2 (G : Type*) [Magma G] (h : Equation23812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


