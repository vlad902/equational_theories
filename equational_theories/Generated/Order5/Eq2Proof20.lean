import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation40996_implies_Equation2 (G : Type*) [Magma G] (h : Equation40996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation40997_implies_Equation2 (G : Type*) [Magma G] (h : Equation40997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40998_implies_Equation2 (G : Type*) [Magma G] (h : Equation40998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40999_implies_Equation2 (G : Type*) [Magma G] (h : Equation40999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation41001_implies_Equation2 (G : Type*) [Magma G] (h : Equation41001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation41002_implies_Equation2 (G : Type*) [Magma G] (h : Equation41002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation41003_implies_Equation2 (G : Type*) [Magma G] (h : Equation41003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X3) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X4 ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41004_implies_Equation2 (G : Type*) [Magma G] (h : Equation41004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation41005_implies_Equation2 (G : Type*) [Magma G] (h : Equation41005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X6 : G) : (X0 ◇ X6) = X2 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation41008_implies_Equation2 (G : Type*) [Magma G] (h : Equation41008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq10 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = X0 := superpose eq10 eq11
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq10 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41011_implies_Equation2 (G : Type*) [Magma G] (h : Equation41011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X2) ◇ ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq16 eq7
  have eq27 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = X0 := superpose eq16 eq19
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq16 eq27
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq16 eq28
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation41013_implies_Equation2 (G : Type*) [Magma G] (h : Equation41013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) := superpose eq10 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq10 eq12
  have eq20 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq10 eq9
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq9 eq7
  have eq31 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq20
  have eq32 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq31 eq10
  have eq34 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq32 eq7
  have eq54 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq28 eq34
  have eq63 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq28 eq54
  have eq64 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq28 eq63
  have eq79 (X0 X2 : G) : X0 = X2 := superpose eq64 eq64
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq81 eq79


@[equational_result]
theorem Equation41014_implies_Equation2 (G : Type*) [Magma G] (h : Equation41014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) := superpose eq10 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X1) := superpose eq10 eq12
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X2) = X0 := superpose eq14 eq7
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq29 eq23


@[equational_result]
theorem Equation41015_implies_Equation2 (G : Type*) [Magma G] (h : Equation41015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X4) = X2 := superpose eq12 eq10
  have eq15 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq12 eq14
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation41018_implies_Equation2 (G : Type*) [Magma G] (h : Equation41018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41021_implies_Equation2 (G : Type*) [Magma G] (h : Equation41021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X1)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ X2)) ◇ X3) = X1 := superpose eq7 eq9
  have eq24 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq12
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq7 eq24
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq140 eq34


@[equational_result]
theorem Equation41023_implies_Equation2 (G : Type*) [Magma G] (h : Equation41023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X1) = X0 := superpose eq11 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq26 eq20


@[equational_result]
theorem Equation41025_implies_Equation2 (G : Type*) [Magma G] (h : Equation41025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41027_implies_Equation2 (G : Type*) [Magma G] (h : Equation41027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq10 eq9
  have eq16 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq10 eq9
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = (((X0 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) := superpose eq9 eq7
  have eq25 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq16
  have eq34 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ X0) = X1 := superpose eq25 eq19
  have eq38 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq25 eq14
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq38 eq25
  have eq61 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq52 eq34
  have eq62 (X0 X1 : G) : X0 = X1 := superpose eq10 eq61
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq85 eq62


@[equational_result]
theorem Equation41028_implies_Equation2 (G : Type*) [Magma G] (h : Equation41028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq39 eq13


@[equational_result]
theorem Equation41029_implies_Equation2 (G : Type*) [Magma G] (h : Equation41029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ X4) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq10 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = X0 := superpose eq10 eq7
  have eq13 (X3 X4 X5 : G) : (X4 ◇ X5) = X3 := superpose eq12 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq25 eq14


@[equational_result]
theorem Equation41031_implies_Equation2 (G : Type*) [Magma G] (h : Equation41031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := superpose eq9 eq7
  have eq13 (X0 X1 : G) : ((((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq7
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq13
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq69 eq27


@[equational_result]
theorem Equation41033_implies_Equation2 (G : Type*) [Magma G] (h : Equation41033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = X1 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq41 eq15


@[equational_result]
theorem Equation41036_implies_Equation2 (G : Type*) [Magma G] (h : Equation41036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq12
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq15 eq10
  have eq18 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq17 eq12
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq18 eq18
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation41037_implies_Equation2 (G : Type*) [Magma G] (h : Equation41037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = X1 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation41039_implies_Equation2 (G : Type*) [Magma G] (h : Equation41039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq56 eq14


@[equational_result]
theorem Equation41040_implies_Equation2 (G : Type*) [Magma G] (h : Equation41040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = X1 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation41041_implies_Equation2 (G : Type*) [Magma G] (h : Equation41041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation41042_implies_Equation2 (G : Type*) [Magma G] (h : Equation41042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X6) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41045_implies_Equation2 (G : Type*) [Magma G] (h : Equation41045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = X1 := superpose eq12 eq10
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = X1 := superpose eq12 eq13
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq12 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation41048_implies_Equation2 (G : Type*) [Magma G] (h : Equation41048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ X2) = X1 := superpose eq7 eq9
  have eq23 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq14
  have eq28 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq23 eq7
  have eq34 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X1 := superpose eq23 eq14
  have eq43 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = X1 := superpose eq28 eq34
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq66 eq56


@[equational_result]
theorem Equation41050_implies_Equation2 (G : Type*) [Magma G] (h : Equation41050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq9 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq31 eq15


@[equational_result]
theorem Equation41051_implies_Equation2 (G : Type*) [Magma G] (h : Equation41051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq9 eq9
  have eq20 (X2 X3 : G) : (X3 ◇ X3) = X2 := superpose eq16 eq9
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation41052_implies_Equation2 (G : Type*) [Magma G] (h : Equation41052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41055_implies_Equation2 (G : Type*) [Magma G] (h : Equation41055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) ◇ X2) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X2) = X1 := superpose eq7 eq10
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation41057_implies_Equation2 (G : Type*) [Magma G] (h : Equation41057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41058_implies_Equation2 (G : Type*) [Magma G] (h : Equation41058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41060_implies_Equation2 (G : Type*) [Magma G] (h : Equation41060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41061_implies_Equation2 (G : Type*) [Magma G] (h : Equation41061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41062_implies_Equation2 (G : Type*) [Magma G] (h : Equation41062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41064_implies_Equation2 (G : Type*) [Magma G] (h : Equation41064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ X1) := superpose eq9 eq7
  have eq25 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq13 eq7
  have eq29 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq25 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq9 eq29
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq49 eq30


@[equational_result]
theorem Equation41065_implies_Equation2 (G : Type*) [Magma G] (h : Equation41065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq7 eq9
  have eq13 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ X0) := superpose eq9 eq7
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq9 eq10
  have eq17 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X2) := superpose eq13 eq13
  have eq25 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq13 eq9
  have eq39 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) = X2 := superpose eq17 eq7
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq39 eq14
  have eq49 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq48 eq7
  have eq55 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := superpose eq48 eq25
  have eq63 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq48 eq55
  have eq64 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq63 eq49
  have eq88 (X0 X1 : G) : X0 = X1 := superpose eq64 eq63
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq112 eq88


@[equational_result]
theorem Equation41066_implies_Equation2 (G : Type*) [Magma G] (h : Equation41066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation41068_implies_Equation2 (G : Type*) [Magma G] (h : Equation41068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41069_implies_Equation2 (G : Type*) [Magma G] (h : Equation41069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41070_implies_Equation2 (G : Type*) [Magma G] (h : Equation41070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41072_implies_Equation2 (G : Type*) [Magma G] (h : Equation41072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41073_implies_Equation2 (G : Type*) [Magma G] (h : Equation41073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41074_implies_Equation2 (G : Type*) [Magma G] (h : Equation41074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41076_implies_Equation2 (G : Type*) [Magma G] (h : Equation41076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41077_implies_Equation2 (G : Type*) [Magma G] (h : Equation41077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41078_implies_Equation2 (G : Type*) [Magma G] (h : Equation41078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41079_implies_Equation2 (G : Type*) [Magma G] (h : Equation41079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41081_implies_Equation2 (G : Type*) [Magma G] (h : Equation41081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq10 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0) := superpose eq10 eq7
  have eq13 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq10 eq12
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq7
  have eq21 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq18 eq13
  have eq23 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq18 eq7
  have eq24 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq9
  have eq26 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq18 eq11
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq18 eq21
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq29 eq24
  have eq36 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq23 eq23
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq36 eq23
  have eq45 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X2) := superpose eq36 eq44
  have eq46 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq29 eq45
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq46 eq26
  have eq54 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq48 eq29
  have eq55 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq54 eq30
  have eq64 (X0 X2 : G) : X0 = X2 := superpose eq55 eq55
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq72 eq64


@[equational_result]
theorem Equation41083_implies_Equation2 (G : Type*) [Magma G] (h : Equation41083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ X4) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq10 eq7
  have eq13 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq12 eq9
  have eq15 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ X5) = X4 := superpose eq12 eq13
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq12 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation41085_implies_Equation2 (G : Type*) [Magma G] (h : Equation41085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq9 eq7
  have eq15 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) = X0 := superpose eq9 eq10
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X2) := superpose eq10 eq10
  have eq43 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ X0) := superpose eq16 eq7
  have eq65 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq15 eq43
  have eq69 (X0 X2 : G) : (((X0 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X2 := superpose eq65 eq11
  have eq70 (X0 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) = X0 := superpose eq65 eq15
  have eq82 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq65 eq70
  have eq83 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq82 eq65
  have eq84 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq83 eq82
  have eq85 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X0) = X2 := superpose eq83 eq69
  have eq87 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq84 eq85
  have eq88 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq84 eq87
  have eq151 (X0 X2 : G) : X0 = X2 := superpose eq88 eq88
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq151 eq8
  subsumption eq153 eq151


@[equational_result]
theorem Equation41086_implies_Equation2 (G : Type*) [Magma G] (h : Equation41086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq32 eq11


@[equational_result]
theorem Equation41087_implies_Equation2 (G : Type*) [Magma G] (h : Equation41087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation41090_implies_Equation2 (G : Type*) [Magma G] (h : Equation41090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq7 eq9
  have eq15 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq11 eq9
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq15 eq11
  have eq18 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq15 eq7
  have eq19 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X2) ◇ X2) = X3 := superpose eq18 eq18
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose eq15 eq18
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq16 eq23
  have eq25 (X2 X3 : G) : ((X3 ◇ X2) ◇ X2) = X3 := superpose eq24 eq19
  have eq28 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq24 eq25
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq28 eq28
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq35 eq30


@[equational_result]
theorem Equation41091_implies_Equation2 (G : Type*) [Magma G] (h : Equation41091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ X2) := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq11
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq124 eq45


@[equational_result]
theorem Equation41093_implies_Equation2 (G : Type*) [Magma G] (h : Equation41093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation41094_implies_Equation2 (G : Type*) [Magma G] (h : Equation41094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq9 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41095_implies_Equation2 (G : Type*) [Magma G] (h : Equation41095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41096_implies_Equation2 (G : Type*) [Magma G] (h : Equation41096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41098_implies_Equation2 (G : Type*) [Magma G] (h : Equation41098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq11 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq14 eq14
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq10 eq17
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq31 eq19


@[equational_result]
theorem Equation41100_implies_Equation2 (G : Type*) [Magma G] (h : Equation41100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = X1 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq57 eq17


@[equational_result]
theorem Equation41102_implies_Equation2 (G : Type*) [Magma G] (h : Equation41102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41103_implies_Equation2 (G : Type*) [Magma G] (h : Equation41103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41104_implies_Equation2 (G : Type*) [Magma G] (h : Equation41104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41106_implies_Equation2 (G : Type*) [Magma G] (h : Equation41106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41107_implies_Equation2 (G : Type*) [Magma G] (h : Equation41107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41108_implies_Equation2 (G : Type*) [Magma G] (h : Equation41108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41110_implies_Equation2 (G : Type*) [Magma G] (h : Equation41110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41111_implies_Equation2 (G : Type*) [Magma G] (h : Equation41111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41112_implies_Equation2 (G : Type*) [Magma G] (h : Equation41112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41113_implies_Equation2 (G : Type*) [Magma G] (h : Equation41113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41116_implies_Equation2 (G : Type*) [Magma G] (h : Equation41116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (((((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X2 := superpose eq7 eq9
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq9
  have eq23 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq7 eq16
  have eq28 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq20 eq7
  have eq30 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X2) = X3 := superpose eq28 eq28
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq23 eq30
  have eq47 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq41 eq30
  have eq54 (X0 X2 : G) : X0 = X2 := superpose eq47 eq47
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq59 eq54


@[equational_result]
theorem Equation41117_implies_Equation2 (G : Type*) [Magma G] (h : Equation41117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation41119_implies_Equation2 (G : Type*) [Magma G] (h : Equation41119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41120_implies_Equation2 (G : Type*) [Magma G] (h : Equation41120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41121_implies_Equation2 (G : Type*) [Magma G] (h : Equation41121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41123_implies_Equation2 (G : Type*) [Magma G] (h : Equation41123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation41124_implies_Equation2 (G : Type*) [Magma G] (h : Equation41124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41125_implies_Equation2 (G : Type*) [Magma G] (h : Equation41125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41127_implies_Equation2 (G : Type*) [Magma G] (h : Equation41127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41128_implies_Equation2 (G : Type*) [Magma G] (h : Equation41128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41129_implies_Equation2 (G : Type*) [Magma G] (h : Equation41129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41130_implies_Equation2 (G : Type*) [Magma G] (h : Equation41130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41132_implies_Equation2 (G : Type*) [Magma G] (h : Equation41132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq34 eq13


@[equational_result]
theorem Equation41133_implies_Equation2 (G : Type*) [Magma G] (h : Equation41133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ X2) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq63 eq52


@[equational_result]
theorem Equation41134_implies_Equation2 (G : Type*) [Magma G] (h : Equation41134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation41135_implies_Equation2 (G : Type*) [Magma G] (h : Equation41135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41137_implies_Equation2 (G : Type*) [Magma G] (h : Equation41137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41138_implies_Equation2 (G : Type*) [Magma G] (h : Equation41138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41139_implies_Equation2 (G : Type*) [Magma G] (h : Equation41139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41140_implies_Equation2 (G : Type*) [Magma G] (h : Equation41140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41142_implies_Equation2 (G : Type*) [Magma G] (h : Equation41142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41143_implies_Equation2 (G : Type*) [Magma G] (h : Equation41143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41144_implies_Equation2 (G : Type*) [Magma G] (h : Equation41144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41145_implies_Equation2 (G : Type*) [Magma G] (h : Equation41145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41147_implies_Equation2 (G : Type*) [Magma G] (h : Equation41147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41148_implies_Equation2 (G : Type*) [Magma G] (h : Equation41148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41149_implies_Equation2 (G : Type*) [Magma G] (h : Equation41149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41150_implies_Equation2 (G : Type*) [Magma G] (h : Equation41150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41152_implies_Equation2 (G : Type*) [Magma G] (h : Equation41152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41153_implies_Equation2 (G : Type*) [Magma G] (h : Equation41153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41154_implies_Equation2 (G : Type*) [Magma G] (h : Equation41154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41155_implies_Equation2 (G : Type*) [Magma G] (h : Equation41155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41156_implies_Equation2 (G : Type*) [Magma G] (h : Equation41156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41158_implies_Equation2 (G : Type*) [Magma G] (h : Equation41158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq15 (X0 X2 : G) : ((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq12 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq12 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq14 eq11
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq12 eq16
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq12 eq18
  have eq25 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ X0) := superpose eq17 eq7
  have eq26 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq25
  have eq27 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq26
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq14 eq7
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq31
  have eq33 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq32 eq27
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq33 eq32
  have eq35 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq34 eq19
  have eq37 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq35 eq15
  have eq44 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq35 eq37
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq44 eq34
  have eq46 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq45 eq12
  have eq54 (X0 X1 : G) : X0 = X1 := superpose eq46 eq45
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq56 eq54


@[equational_result]
theorem Equation41159_implies_Equation2 (G : Type*) [Magma G] (h : Equation41159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((((X0 ◇ X3) ◇ X3) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq12 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq12 eq15
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq12 eq16
  have eq18 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq17 eq7
  have eq19 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X3) ◇ X2) = X3 := superpose eq17 eq9
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq17 eq18
  have eq22 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq17 eq19
  have eq24 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq22 eq21
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq24 eq24
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq32 eq27


@[equational_result]
theorem Equation41160_implies_Equation2 (G : Type*) [Magma G] (h : Equation41160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq13 eq10
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation41162_implies_Equation2 (G : Type*) [Magma G] (h : Equation41162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = X2 := superpose eq11 eq11
  have eq20 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq14 eq10
  have eq22 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq14 eq7
  have eq41 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X2 ◇ X3) ◇ X0) ◇ X2) := superpose eq15 eq11
  have eq44 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) = X1 := superpose eq22 eq20
  have eq64 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq44
  have eq65 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X2) = X0 := superpose eq64 eq41
  have eq69 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq65 eq15
  have eq77 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq69 eq20
  have eq90 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq69 eq77
  have eq91 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq69 eq90
  have eq92 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq69 eq91
  have eq95 (X0 X1 : G) : X0 = X1 := superpose eq92 eq69
  have eq97 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq97 eq95


@[equational_result]
theorem Equation41163_implies_Equation2 (G : Type*) [Magma G] (h : Equation41163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X3) ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1)) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq11 eq7
  have eq13 (X0 X1 X2 : G) : ((((X0 ◇ X2) ◇ X2) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X1) = X2 := superpose eq11 eq7
  have eq37 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq12 eq11
  have eq59 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((((X1 ◇ X0) ◇ X0) ◇ ((((X2 ◇ X3) ◇ X1) ◇ X1) ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((((X2 ◇ X3) ◇ X1) ◇ X1) ◇ X2))) ◇ X3)) = X3 := superpose eq9 eq12
  have eq69 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq37
  have eq76 (X0 X1 : G) : (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq37 eq7
  have eq79 (X0 X1 X2 : G) : (X1 ◇ X2) = ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X1) ◇ X2) := superpose eq37 eq7
  have eq108 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq12 eq13
  have eq110 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq13 eq7
  have eq120 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq69 eq108
  have eq123 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq120 eq69
  have eq127 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq123 eq37
  have eq154 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq127 eq110
  have eq158 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq123 eq154
  have eq163 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((((X1 ◇ X0) ◇ X0) ◇ ((((X2 ◇ X3) ◇ X1) ◇ X1) ◇ X2)) ◇ X3)) = X3 := superpose eq158 eq59
  have eq224 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X3 := superpose eq9 eq163
  have eq226 (X0 X1 X2 : G) : (X1 ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X2) := superpose eq224 eq79
  have eq233 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq224 eq76
  have eq239 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq224 eq233
  have eq240 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq239 eq7
  have eq271 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq240 eq226
  have eq272 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq239 eq271
  have eq278 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq272 eq240
  have eq282 (X0 X3 : G) : X0 = X3 := superpose eq278 eq278
  have eq284 (X0 : G) : sK0 ≠ X0 := superpose eq282 eq8
  subsumption eq284 eq282


@[equational_result]
theorem Equation41164_implies_Equation2 (G : Type*) [Magma G] (h : Equation41164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ X4) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ X5) = X4 := superpose eq12 eq9
  have eq17 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ X5) = X4 := superpose eq12 eq13
  have eq18 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq12 eq17
  have eq19 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation41167_implies_Equation2 (G : Type*) [Magma G] (h : Equation41167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq12 eq11
  have eq21 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq26 eq21


@[equational_result]
theorem Equation41168_implies_Equation2 (G : Type*) [Magma G] (h : Equation41168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq13 eq10
  have eq16 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation41170_implies_Equation2 (G : Type*) [Magma G] (h : Equation41170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X4) ◇ X4) ◇ X5) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X3)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq12
  have eq21 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ X4) ◇ X5) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) = X4 := superpose eq13 eq9
  have eq26 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ X4) ◇ X5) ◇ ((X1 ◇ X2) ◇ X0)) = X4 := superpose eq13 eq21
  have eq27 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ X4) ◇ X5) ◇ (X1 ◇ X2)) = X4 := superpose eq13 eq26
  have eq28 (X0 X1 X4 X5 : G) : ((((X0 ◇ X4) ◇ X4) ◇ X5) ◇ X1) = X4 := superpose eq13 eq27
  have eq29 (X0 X1 X4 : G) : (((X0 ◇ X4) ◇ X4) ◇ X1) = X4 := superpose eq13 eq28
  have eq30 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ X1) = X4 := superpose eq13 eq29
  have eq31 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq13 eq30
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation41171_implies_Equation2 (G : Type*) [Magma G] (h : Equation41171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X4) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq13 eq10
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation41172_implies_Equation2 (G : Type*) [Magma G] (h : Equation41172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X0 := superpose eq10 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq20 eq17


@[equational_result]
theorem Equation41173_implies_Equation2 (G : Type*) [Magma G] (h : Equation41173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (((X0 ◇ X4) ◇ X5) ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X4 X6 : G) : ((X0 ◇ X4) ◇ X6) = X4 := superpose eq13 eq10
  have eq16 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation41175_implies_Equation2 (G : Type*) [Magma G] (h : Equation41175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq11
  have eq17 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq12 eq7
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X1 := superpose eq13 eq10
  have eq19 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X1 := superpose eq17 eq18
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq11 eq13
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq24 eq19
  have eq42 (X0 X1 : G) : X0 = X1 := superpose eq17 eq33
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq50 eq42


@[equational_result]
theorem Equation41176_implies_Equation2 (G : Type*) [Magma G] (h : Equation41176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X1) ◇ X2) = (((X0 ◇ X0) ◇ (((X2 ◇ X0) ◇ X1) ◇ X2)) ◇ X0) := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X2 ◇ X0) ◇ X1) ◇ X2)) = X0 := superpose eq10 eq7
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X2 ◇ X0) ◇ X1) ◇ X2) := superpose eq21 eq20
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X2)) ◇ X0)) = (X1 ◇ X1) := superpose eq10 eq24
  have eq31 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X1) := superpose eq24 eq24
  have eq32 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = (X0 ◇ X0) := superpose eq7 eq24
  have eq38 (X0 X1 X2 X3 : G) : (((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X1) ◇ X3) ◇ X1) = X3 := superpose eq24 eq7
  have eq48 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) = X1 := superpose eq24 eq7
  have eq49 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq24 eq10
  have eq56 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X3) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq32 eq28
  have eq62 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq31 eq38
  have eq64 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X1 := superpose eq49 eq48
  have eq66 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X0 ◇ X3) ◇ X1) := superpose eq64 eq56
  have eq79 (X0 X1 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq66 eq62
  have eq86 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq64 eq79
  have eq98 (X0 X1 : G) : X0 = X1 := superpose eq11 eq86
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq142 eq98


@[equational_result]
theorem Equation41177_implies_Equation2 (G : Type*) [Magma G] (h : Equation41177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4) ◇ X5) = X4 := superpose eq12 eq9
  have eq16 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq12 eq13
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq12 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq28 eq24


@[equational_result]
theorem Equation41180_implies_Equation2 (G : Type*) [Magma G] (h : Equation41180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq16 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) := superpose eq10 eq7
  have eq28 (X0 X1 X2 : G) : (((((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) = X2 := superpose eq10 eq9
  have eq55 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = ((((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq16 eq15
  have eq56 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq7 eq15
  have eq66 (X0 X1 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq7 eq55
  have eq68 (X0 X1 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X1 := superpose eq56 eq9
  have eq70 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq56 eq7
  have eq83 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq70 eq56
  have eq86 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq83 eq68
  have eq90 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) = X1 := superpose eq83 eq86
  have eq162 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) := superpose eq83 eq7
  have eq175 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X1) := superpose eq162 eq15
  have eq201 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq16 eq175
  have eq206 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq175 eq7
  have eq211 (X0 X1 : G) : ((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq175 eq7
  have eq249 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq83 eq201
  have eq250 (X0 X1 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq66 eq249
  have eq266 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = ((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq16 eq90
  have eq290 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq250 eq266
  have eq291 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq83 eq290
  have eq292 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq83 eq291
  have eq296 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X2 := superpose eq292 eq28
  have eq342 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X2 := superpose eq292 eq296
  have eq344 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq342 eq211
  have eq393 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq344 eq206
  have eq395 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq393 eq7
  have eq413 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq393 eq395
  have eq414 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq393 eq413
  have eq415 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq393 eq414
  have eq416 (X0 X1 : G) : X0 = X1 := superpose eq83 eq415
  have eq421 (X0 : G) : sK0 ≠ X0 := superpose eq416 eq8
  subsumption eq421 eq416


@[equational_result]
theorem Equation41181_implies_Equation2 (G : Type*) [Magma G] (h : Equation41181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X4) = X3 := superpose eq7 eq7
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq56 eq39


@[equational_result]
theorem Equation41185_implies_Equation2 (G : Type*) [Magma G] (h : Equation41185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq68 eq15


@[equational_result]
theorem Equation41187_implies_Equation2 (G : Type*) [Magma G] (h : Equation41187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq38 eq16


@[equational_result]
theorem Equation41188_implies_Equation2 (G : Type*) [Magma G] (h : Equation41188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation41189_implies_Equation2 (G : Type*) [Magma G] (h : Equation41189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq53 eq17


@[equational_result]
theorem Equation41190_implies_Equation2 (G : Type*) [Magma G] (h : Equation41190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation41192_implies_Equation2 (G : Type*) [Magma G] (h : Equation41192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq31 eq14


@[equational_result]
theorem Equation41193_implies_Equation2 (G : Type*) [Magma G] (h : Equation41193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((((X0 ◇ X3) ◇ X2) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq9 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41194_implies_Equation2 (G : Type*) [Magma G] (h : Equation41194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((((X0 ◇ X4) ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41198_implies_Equation2 (G : Type*) [Magma G] (h : Equation41198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation41201_implies_Equation2 (G : Type*) [Magma G] (h : Equation41201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41202_implies_Equation2 (G : Type*) [Magma G] (h : Equation41202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41204_implies_Equation2 (G : Type*) [Magma G] (h : Equation41204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation41205_implies_Equation2 (G : Type*) [Magma G] (h : Equation41205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation41206_implies_Equation2 (G : Type*) [Magma G] (h : Equation41206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq43 eq13


@[equational_result]
theorem Equation41207_implies_Equation2 (G : Type*) [Magma G] (h : Equation41207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X4) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41209_implies_Equation2 (G : Type*) [Magma G] (h : Equation41209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq35 eq15


@[equational_result]
theorem Equation41210_implies_Equation2 (G : Type*) [Magma G] (h : Equation41210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq33 eq13


@[equational_result]
theorem Equation41211_implies_Equation2 (G : Type*) [Magma G] (h : Equation41211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (((X0 ◇ X4) ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41212_implies_Equation2 (G : Type*) [Magma G] (h : Equation41212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (((X0 ◇ X5) ◇ X4) ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41214_implies_Equation2 (G : Type*) [Magma G] (h : Equation41214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X4) ◇ X5) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq10
  have eq46 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X4) ◇ X5) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X4 := superpose eq34 eq9
  have eq75 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ X5) ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) = X4 := superpose eq34 eq46
  have eq76 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ X5) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = X4 := superpose eq34 eq75
  have eq77 (X0 X1 X4 X5 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X1) ◇ X1) = X4 := superpose eq34 eq76
  have eq78 (X0 X1 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X1) = X4 := superpose eq34 eq77
  have eq79 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ X1) = X4 := superpose eq34 eq78
  have eq80 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq34 eq79
  have eq81 (X0 X3 : G) : X0 = X3 := superpose eq80 eq80
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq83 eq81


@[equational_result]
theorem Equation41215_implies_Equation2 (G : Type*) [Magma G] (h : Equation41215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) = X1 := superpose eq7 eq7
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq11 eq11
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq134 eq43


@[equational_result]
theorem Equation41216_implies_Equation2 (G : Type*) [Magma G] (h : Equation41216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X4) ◇ X5) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1)) = X0 := superpose eq7 eq12
  have eq29 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq13 eq9
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq29
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq49 eq30


@[equational_result]
theorem Equation41217_implies_Equation2 (G : Type*) [Magma G] (h : Equation41217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation41219_implies_Equation2 (G : Type*) [Magma G] (h : Equation41219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation41220_implies_Equation2 (G : Type*) [Magma G] (h : Equation41220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq43 eq13


@[equational_result]
theorem Equation41221_implies_Equation2 (G : Type*) [Magma G] (h : Equation41221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X3) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X3) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation41222_implies_Equation2 (G : Type*) [Magma G] (h : Equation41222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X4) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41224_implies_Equation2 (G : Type*) [Magma G] (h : Equation41224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation41225_implies_Equation2 (G : Type*) [Magma G] (h : Equation41225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41226_implies_Equation2 (G : Type*) [Magma G] (h : Equation41226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq11 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41227_implies_Equation2 (G : Type*) [Magma G] (h : Equation41227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation41229_implies_Equation2 (G : Type*) [Magma G] (h : Equation41229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq61 eq16


@[equational_result]
theorem Equation41230_implies_Equation2 (G : Type*) [Magma G] (h : Equation41230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ X2) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41231_implies_Equation2 (G : Type*) [Magma G] (h : Equation41231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation41232_implies_Equation2 (G : Type*) [Magma G] (h : Equation41232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation41233_implies_Equation2 (G : Type*) [Magma G] (h : Equation41233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X6 X7 X8 X9 : G) : ((((X0 ◇ X6) ◇ X7) ◇ X8) ◇ X9) = X6 := superpose eq7 eq7
  have eq13 (X0 X2 X5 : G) : (X2 ◇ X5) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41235_implies_Equation2 (G : Type*) [Magma G] (h : Equation41235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X0)) ◇ X3) ◇ X3) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq10 eq7
  have eq19 (X0 X1 X3 : G) : ((((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X1)) = X3 := superpose eq10 eq9
  have eq62 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq14 eq19
  have eq63 (X0 X1 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq19
  have eq69 (X0 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq19
  have eq82 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq14 eq62
  have eq103 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq14 eq82
  have eq111 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq82 eq14
  have eq125 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq82 eq103
  have eq127 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq125 eq69
  have eq132 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq111 eq13
  have eq140 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq125 eq132
  have eq217 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq140 eq140
  have eq219 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq140 eq127
  have eq225 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq125 eq219
  have eq226 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq225 eq217
  have eq227 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq226 eq63
  have eq233 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X0) = X3 := superpose eq226 eq227
  have eq234 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = X3 := superpose eq226 eq233
  have eq235 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq226 eq234
  have eq236 (X0 X1 : G) : X0 = X1 := superpose eq125 eq235
  have eq244 (X0 : G) : sK0 ≠ X0 := superpose eq236 eq8
  subsumption eq244 eq236


@[equational_result]
theorem Equation41236_implies_Equation2 (G : Type*) [Magma G] (h : Equation41236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X0)) ◇ X3) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) := superpose eq10 eq10
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq10 eq10
  have eq19 (X0 X1 X3 : G) : ((((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq10 eq9
  have eq24 (X0 X1 : G) : (X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0)) = X0 := superpose eq9 eq7
  have eq31 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq13 eq7
  have eq32 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X0)) = ((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X0)) ◇ X2) := superpose eq13 eq9
  have eq36 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X0 := superpose eq31 eq24
  have eq40 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := superpose eq31 eq12
  have eq41 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq31 eq10
  have eq42 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq31 eq36
  have eq46 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose eq42 eq40
  have eq47 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ X0) := superpose eq42 eq46
  have eq56 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq41
  have eq68 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq56 eq47
  have eq80 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X0)) = ((X0 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X2) := superpose eq68 eq32
  have eq98 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq68 eq68
  have eq99 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq98 eq19
  have eq102 (X0 X2 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ X2) := superpose eq98 eq80
  have eq109 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq68 eq102
  have eq110 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq109 eq99
  have eq119 (X0 X1 : G) : X0 = X1 := superpose eq110 eq109
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq121 eq119


@[equational_result]
theorem Equation41237_implies_Equation2 (G : Type*) [Magma G] (h : Equation41237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ X3) = X2 := superpose eq14 eq11
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = X2 := superpose eq14 eq15
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq14 eq17
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation41240_implies_Equation2 (G : Type*) [Magma G] (h : Equation41240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1)) ◇ X3) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1)) ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1)) = X2 := superpose eq9 eq9
  have eq15 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq12
  have eq25 (X0 X1 X2 X3 : G) : ((((((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq15 eq9
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X2 ◇ X1) ◇ X2) ◇ X1) ◇ X2) := superpose eq15 eq7
  have eq46 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ ((((X3 ◇ X2) ◇ X3) ◇ X2) ◇ X3)) = X1 := superpose eq26 eq15
  have eq57 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq26 eq7
  have eq75 (X0 X1 X2 X3 : G) : (((((X2 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq57 eq25
  have eq88 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((((X3 ◇ X2) ◇ X3) ◇ X2) ◇ X3)) = X1 := superpose eq57 eq46
  have eq103 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = X1 := superpose eq57 eq88
  have eq104 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq103 eq75
  have eq117 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq103 eq104
  have eq122 (X0 X3 : G) : X0 = X3 := superpose eq7 eq117
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq8
  subsumption eq172 eq122


@[equational_result]
theorem Equation41241_implies_Equation2 (G : Type*) [Magma G] (h : Equation41241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1)) ◇ X4) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X1)) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X5) = X4 := superpose eq11 eq9
  have eq15 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X5) = X4 := superpose eq11 eq12
  have eq16 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ X5) = X4 := superpose eq11 eq15
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq16 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq28 eq21


@[equational_result]
theorem Equation41243_implies_Equation2 (G : Type*) [Magma G] (h : Equation41243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq10
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq10 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq74 eq26


@[equational_result]
theorem Equation41244_implies_Equation2 (G : Type*) [Magma G] (h : Equation41244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq10 eq7
  have eq25 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq11
  have eq27 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq11 eq7
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq25 eq27
  have eq98 (X0 X2 : G) : X0 = X2 := superpose eq39 eq39
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq103 eq98


@[equational_result]
theorem Equation41245_implies_Equation2 (G : Type*) [Magma G] (h : Equation41245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41247_implies_Equation2 (G : Type*) [Magma G] (h : Equation41247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation41248_implies_Equation2 (G : Type*) [Magma G] (h : Equation41248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq54 eq15


@[equational_result]
theorem Equation41249_implies_Equation2 (G : Type*) [Magma G] (h : Equation41249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3)) ◇ X4) ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ X4) ◇ X5) ◇ X5) = X4 := superpose eq12 eq9
  have eq16 (X4 X5 : G) : (X5 ◇ X5) = X4 := superpose eq12 eq13
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation41250_implies_Equation2 (G : Type*) [Magma G] (h : Equation41250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (((X0 ◇ X4) ◇ X5) ◇ X6) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41254_implies_Equation2 (G : Type*) [Magma G] (h : Equation41254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41256_implies_Equation2 (G : Type*) [Magma G] (h : Equation41256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41257_implies_Equation2 (G : Type*) [Magma G] (h : Equation41257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41258_implies_Equation2 (G : Type*) [Magma G] (h : Equation41258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41260_implies_Equation2 (G : Type*) [Magma G] (h : Equation41260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41261_implies_Equation2 (G : Type*) [Magma G] (h : Equation41261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41262_implies_Equation2 (G : Type*) [Magma G] (h : Equation41262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41264_implies_Equation2 (G : Type*) [Magma G] (h : Equation41264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41265_implies_Equation2 (G : Type*) [Magma G] (h : Equation41265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41266_implies_Equation2 (G : Type*) [Magma G] (h : Equation41266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41267_implies_Equation2 (G : Type*) [Magma G] (h : Equation41267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41269_implies_Equation2 (G : Type*) [Magma G] (h : Equation41269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X0)) ◇ X1) ◇ X3) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X1 ◇ X1) ◇ X1)) = X2 := superpose eq10 eq7
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq10 eq7
  have eq15 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) = X2 := superpose eq13 eq12
  have eq18 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq9
  have eq23 (X0 X1 X2 : G) : ((((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0)) ◇ X0) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0)) = X2 := superpose eq9 eq9
  have eq24 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) ◇ X0) := superpose eq9 eq7
  have eq27 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq7 eq24
  have eq28 (X0 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq27 eq23
  have eq29 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq13 eq28
  have eq41 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq13 eq29
  have eq47 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq41 eq13
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X1)) = X2 := superpose eq47 eq15
  have eq54 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq47 eq48
  have eq56 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ X2))) = X3 := superpose eq54 eq18
  have eq64 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X2) ◇ X1) = X3 := superpose eq54 eq56
  have eq65 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq54 eq64
  have eq66 (X0 X1 : G) : X0 = X1 := superpose eq47 eq65
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq71 eq66


@[equational_result]
theorem Equation41271_implies_Equation2 (G : Type*) [Magma G] (h : Equation41271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41273_implies_Equation2 (G : Type*) [Magma G] (h : Equation41273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41274_implies_Equation2 (G : Type*) [Magma G] (h : Equation41274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41275_implies_Equation2 (G : Type*) [Magma G] (h : Equation41275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41277_implies_Equation2 (G : Type*) [Magma G] (h : Equation41277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41278_implies_Equation2 (G : Type*) [Magma G] (h : Equation41278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41279_implies_Equation2 (G : Type*) [Magma G] (h : Equation41279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41281_implies_Equation2 (G : Type*) [Magma G] (h : Equation41281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41282_implies_Equation2 (G : Type*) [Magma G] (h : Equation41282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41283_implies_Equation2 (G : Type*) [Magma G] (h : Equation41283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41284_implies_Equation2 (G : Type*) [Magma G] (h : Equation41284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41286_implies_Equation2 (G : Type*) [Magma G] (h : Equation41286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq36 eq15


@[equational_result]
theorem Equation41287_implies_Equation2 (G : Type*) [Magma G] (h : Equation41287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41288_implies_Equation2 (G : Type*) [Magma G] (h : Equation41288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41289_implies_Equation2 (G : Type*) [Magma G] (h : Equation41289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (((X0 ◇ X4) ◇ X5) ◇ X6) = X5 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41291_implies_Equation2 (G : Type*) [Magma G] (h : Equation41291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41292_implies_Equation2 (G : Type*) [Magma G] (h : Equation41292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41293_implies_Equation2 (G : Type*) [Magma G] (h : Equation41293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41294_implies_Equation2 (G : Type*) [Magma G] (h : Equation41294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41296_implies_Equation2 (G : Type*) [Magma G] (h : Equation41296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41297_implies_Equation2 (G : Type*) [Magma G] (h : Equation41297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41298_implies_Equation2 (G : Type*) [Magma G] (h : Equation41298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41299_implies_Equation2 (G : Type*) [Magma G] (h : Equation41299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41301_implies_Equation2 (G : Type*) [Magma G] (h : Equation41301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41302_implies_Equation2 (G : Type*) [Magma G] (h : Equation41302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41303_implies_Equation2 (G : Type*) [Magma G] (h : Equation41303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41304_implies_Equation2 (G : Type*) [Magma G] (h : Equation41304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41306_implies_Equation2 (G : Type*) [Magma G] (h : Equation41306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41307_implies_Equation2 (G : Type*) [Magma G] (h : Equation41307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41308_implies_Equation2 (G : Type*) [Magma G] (h : Equation41308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41309_implies_Equation2 (G : Type*) [Magma G] (h : Equation41309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41310_implies_Equation2 (G : Type*) [Magma G] (h : Equation41310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41312_implies_Equation2 (G : Type*) [Magma G] (h : Equation41312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq12 eq7
  have eq15 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq12 eq13
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X1) = X2 := superpose eq15 eq10
  have eq18 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq16 eq7
  have eq19 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq18 eq16
  have eq23 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq19 eq18
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation41313_implies_Equation2 (G : Type*) [Magma G] (h : Equation41313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq11
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq10 eq17
  have eq38 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X2) = X3 := superpose eq36 eq9
  have eq45 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq11 eq38
  have eq55 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq45 eq36
  have eq60 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq55 eq17
  have eq71 (X0 X2 : G) : X0 = X2 := superpose eq60 eq60
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq79 eq71


@[equational_result]
theorem Equation41314_implies_Equation2 (G : Type*) [Magma G] (h : Equation41314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ X4) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq13 eq9
  have eq16 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq14 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41316_implies_Equation2 (G : Type*) [Magma G] (h : Equation41316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X3 ◇ X4) ◇ X4) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X1))) ◇ (((X3 ◇ X4) ◇ X4) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X1))) = X1 := superpose eq7 eq10
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq10 eq11
  have eq114 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq7 eq31
  have eq121 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X1) = (X0 ◇ X1) := superpose eq7 eq31
  have eq161 (X0 X1 X3 X4 : G) : ((X0 ◇ (((X3 ◇ X4) ◇ X4) ◇ ((X1 ◇ X0) ◇ X1))) ◇ (((X3 ◇ X4) ◇ X4) ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose eq114 eq18
  have eq189 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose eq114 eq161
  have eq194 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq114 eq121
  have eq206 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) = X1 := superpose eq194 eq189
  have eq278 (X0 X2 : G) : X0 = X2 := superpose eq114 eq206
  have eq282 (X0 : G) : sK0 ≠ X0 := superpose eq278 eq8
  subsumption eq282 eq278


@[equational_result]
theorem Equation41318_implies_Equation2 (G : Type*) [Magma G] (h : Equation41318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq55 eq13


@[equational_result]
theorem Equation41321_implies_Equation2 (G : Type*) [Magma G] (h : Equation41321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ X3) ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq10 eq10
  have eq22 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq20 eq9
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq32 eq27


@[equational_result]
theorem Equation41322_implies_Equation2 (G : Type*) [Magma G] (h : Equation41322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41324_implies_Equation2 (G : Type*) [Magma G] (h : Equation41324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation41325_implies_Equation2 (G : Type*) [Magma G] (h : Equation41325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41326_implies_Equation2 (G : Type*) [Magma G] (h : Equation41326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ X4) ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq7
  have eq14 (X4 X5 : G) : (X5 ◇ X5) = X4 := superpose eq12 eq9
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq12 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation41327_implies_Equation2 (G : Type*) [Magma G] (h : Equation41327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41330_implies_Equation2 (G : Type*) [Magma G] (h : Equation41330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0)) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq11 eq7
  have eq13 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose eq11 eq7
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq12
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq12
  have eq36 (X0 X1 : G) : ((((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq12 eq10
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq28 eq13
  have eq52 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq29 eq36
  have eq64 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X2 := superpose eq7 eq9
  have eq69 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ ((((X3 ◇ X1) ◇ X1) ◇ X3) ◇ X2)) ◇ X0))) ◇ X4) ◇ X1) = X4 := superpose eq9 eq10
  have eq77 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X1) := superpose eq29 eq7
  have eq87 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq52 eq77
  have eq110 (X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X2 := superpose eq87 eq64
  have eq113 (X0 X1 X2 X4 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0))) ◇ X4) ◇ X1) = X4 := superpose eq87 eq69
  have eq149 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq38 eq110
  have eq156 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq149 eq87
  have eq157 (X0 X1 X2 X4 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2)))) ◇ X4) ◇ X1) = X4 := superpose eq156 eq113
  have eq173 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2)))) ◇ X1) = X4 := superpose eq156 eq157
  have eq174 (X1 X4 : G) : (X1 ◇ X1) = X4 := superpose eq156 eq173
  have eq178 (X0 X2 : G) : X0 = X2 := superpose eq174 eq174
  have eq192 (X0 : G) : sK0 ≠ X0 := superpose eq178 eq8
  subsumption eq192 eq178


@[equational_result]
theorem Equation41331_implies_Equation2 (G : Type*) [Magma G] (h : Equation41331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41333_implies_Equation2 (G : Type*) [Magma G] (h : Equation41333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41334_implies_Equation2 (G : Type*) [Magma G] (h : Equation41334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41335_implies_Equation2 (G : Type*) [Magma G] (h : Equation41335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41337_implies_Equation2 (G : Type*) [Magma G] (h : Equation41337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41338_implies_Equation2 (G : Type*) [Magma G] (h : Equation41338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41339_implies_Equation2 (G : Type*) [Magma G] (h : Equation41339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41341_implies_Equation2 (G : Type*) [Magma G] (h : Equation41341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41342_implies_Equation2 (G : Type*) [Magma G] (h : Equation41342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41343_implies_Equation2 (G : Type*) [Magma G] (h : Equation41343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41344_implies_Equation2 (G : Type*) [Magma G] (h : Equation41344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41347_implies_Equation2 (G : Type*) [Magma G] (h : Equation41347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq28 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq11 eq9
  have eq35 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq12 eq28
  have eq36 (X2 X3 : G) : (X3 ◇ X2) = X3 := superpose eq35 eq9
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq36 eq35
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq46 eq44


@[equational_result]
theorem Equation41348_implies_Equation2 (G : Type*) [Magma G] (h : Equation41348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41350_implies_Equation2 (G : Type*) [Magma G] (h : Equation41350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41351_implies_Equation2 (G : Type*) [Magma G] (h : Equation41351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41352_implies_Equation2 (G : Type*) [Magma G] (h : Equation41352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41354_implies_Equation2 (G : Type*) [Magma G] (h : Equation41354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41355_implies_Equation2 (G : Type*) [Magma G] (h : Equation41355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41356_implies_Equation2 (G : Type*) [Magma G] (h : Equation41356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41358_implies_Equation2 (G : Type*) [Magma G] (h : Equation41358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41359_implies_Equation2 (G : Type*) [Magma G] (h : Equation41359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41360_implies_Equation2 (G : Type*) [Magma G] (h : Equation41360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41361_implies_Equation2 (G : Type*) [Magma G] (h : Equation41361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41363_implies_Equation2 (G : Type*) [Magma G] (h : Equation41363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq37 eq15


@[equational_result]
theorem Equation41364_implies_Equation2 (G : Type*) [Magma G] (h : Equation41364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq13 eq12
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41365_implies_Equation2 (G : Type*) [Magma G] (h : Equation41365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq32 eq13


@[equational_result]
theorem Equation41366_implies_Equation2 (G : Type*) [Magma G] (h : Equation41366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41368_implies_Equation2 (G : Type*) [Magma G] (h : Equation41368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41369_implies_Equation2 (G : Type*) [Magma G] (h : Equation41369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41370_implies_Equation2 (G : Type*) [Magma G] (h : Equation41370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41371_implies_Equation2 (G : Type*) [Magma G] (h : Equation41371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41373_implies_Equation2 (G : Type*) [Magma G] (h : Equation41373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41374_implies_Equation2 (G : Type*) [Magma G] (h : Equation41374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41375_implies_Equation2 (G : Type*) [Magma G] (h : Equation41375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41376_implies_Equation2 (G : Type*) [Magma G] (h : Equation41376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41378_implies_Equation2 (G : Type*) [Magma G] (h : Equation41378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41379_implies_Equation2 (G : Type*) [Magma G] (h : Equation41379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41380_implies_Equation2 (G : Type*) [Magma G] (h : Equation41380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41381_implies_Equation2 (G : Type*) [Magma G] (h : Equation41381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41383_implies_Equation2 (G : Type*) [Magma G] (h : Equation41383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41384_implies_Equation2 (G : Type*) [Magma G] (h : Equation41384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41385_implies_Equation2 (G : Type*) [Magma G] (h : Equation41385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41386_implies_Equation2 (G : Type*) [Magma G] (h : Equation41386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41387_implies_Equation2 (G : Type*) [Magma G] (h : Equation41387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41389_implies_Equation2 (G : Type*) [Magma G] (h : Equation41389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq19 (X0 X1 X4 X5 : G) : (X0 ◇ ((X1 ◇ X4) ◇ X5)) = X1 := superpose eq7 eq11
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq11
  have eq48 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq26 eq19
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq12 eq48
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq65 eq55


@[equational_result]
theorem Equation41390_implies_Equation2 (G : Type*) [Magma G] (h : Equation41390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X2) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X2) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation41391_implies_Equation2 (G : Type*) [Magma G] (h : Equation41391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) := superpose eq12 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ X2) := superpose eq12 eq15
  have eq17 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3) = X0 := superpose eq16 eq7
  have eq21 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq17 eq17
  have eq26 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq21 eq17
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq26 eq26
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation41392_implies_Equation2 (G : Type*) [Magma G] (h : Equation41392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq13 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation41394_implies_Equation2 (G : Type*) [Magma G] (h : Equation41394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq40 eq18


@[equational_result]
theorem Equation41395_implies_Equation2 (G : Type*) [Magma G] (h : Equation41395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X4) ◇ X5) ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1)) ◇ X2) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X4) ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) = X4 := superpose eq11 eq7
  have eq21 (X2 X4 X5 : G) : (X4 ◇ X2) = X5 := superpose eq18 eq9
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq44 eq22


@[equational_result]
theorem Equation41396_implies_Equation2 (G : Type*) [Magma G] (h : Equation41396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq42 eq13


@[equational_result]
theorem Equation41397_implies_Equation2 (G : Type*) [Magma G] (h : Equation41397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation41399_implies_Equation2 (G : Type*) [Magma G] (h : Equation41399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq36 eq15


@[equational_result]
theorem Equation41400_implies_Equation2 (G : Type*) [Magma G] (h : Equation41400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41401_implies_Equation2 (G : Type*) [Magma G] (h : Equation41401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X3) ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq9 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41402_implies_Equation2 (G : Type*) [Magma G] (h : Equation41402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X4) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41404_implies_Equation2 (G : Type*) [Magma G] (h : Equation41404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq48 eq16


@[equational_result]
theorem Equation41405_implies_Equation2 (G : Type*) [Magma G] (h : Equation41405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (((X0 ◇ X4) ◇ X2) ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41406_implies_Equation2 (G : Type*) [Magma G] (h : Equation41406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (((X0 ◇ X4) ◇ X3) ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X2) := superpose eq12 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq10 eq15
  have eq17 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq16 eq7
  have eq20 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation41407_implies_Equation2 (G : Type*) [Magma G] (h : Equation41407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (((X0 ◇ X5) ◇ X4) ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41409_implies_Equation2 (G : Type*) [Magma G] (h : Equation41409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = X4 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation41410_implies_Equation2 (G : Type*) [Magma G] (h : Equation41410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ X2) = X6 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41411_implies_Equation2 (G : Type*) [Magma G] (h : Equation41411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : (((X0 ◇ X5) ◇ X6) ◇ X3) = X5 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41412_implies_Equation2 (G : Type*) [Magma G] (h : Equation41412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41413_implies_Equation2 (G : Type*) [Magma G] (h : Equation41413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X6 X7 X8 X9 : G) : ((((X0 ◇ X6) ◇ X7) ◇ X8) ◇ X9) = X7 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X3 ◇ X5) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41415_implies_Equation2 (G : Type*) [Magma G] (h : Equation41415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) ◇ X4) ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq11
  have eq21 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ ((X0 ◇ X5) ◇ ((((X2 ◇ X3) ◇ X4) ◇ X2) ◇ X0))) ◇ X6) ◇ ((X0 ◇ X5) ◇ ((((X2 ◇ X3) ◇ X4) ◇ X2) ◇ X0))) = X6 := superpose eq7 eq10
  have eq33 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq11 eq13
  have eq52 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ ((X0 ◇ X5) ◇ ((X2 ◇ X3) ◇ X4))) ◇ X6) ◇ ((X0 ◇ X5) ◇ ((X2 ◇ X3) ◇ X4))) = X6 := superpose eq33 eq21
  have eq69 (X0 X1 X6 : G) : (((X1 ◇ X0) ◇ X6) ◇ X0) = X6 := superpose eq33 eq52
  have eq70 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq33 eq69
  have eq71 (X0 X2 : G) : X0 = X2 := superpose eq11 eq70
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq84 eq71


@[equational_result]
theorem Equation41416_implies_Equation2 (G : Type*) [Magma G] (h : Equation41416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41417_implies_Equation2 (G : Type*) [Magma G] (h : Equation41417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation41418_implies_Equation2 (G : Type*) [Magma G] (h : Equation41418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41420_implies_Equation2 (G : Type*) [Magma G] (h : Equation41420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41421_implies_Equation2 (G : Type*) [Magma G] (h : Equation41421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41422_implies_Equation2 (G : Type*) [Magma G] (h : Equation41422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41423_implies_Equation2 (G : Type*) [Magma G] (h : Equation41423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41425_implies_Equation2 (G : Type*) [Magma G] (h : Equation41425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41426_implies_Equation2 (G : Type*) [Magma G] (h : Equation41426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41427_implies_Equation2 (G : Type*) [Magma G] (h : Equation41427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41428_implies_Equation2 (G : Type*) [Magma G] (h : Equation41428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41430_implies_Equation2 (G : Type*) [Magma G] (h : Equation41430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41431_implies_Equation2 (G : Type*) [Magma G] (h : Equation41431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41432_implies_Equation2 (G : Type*) [Magma G] (h : Equation41432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41433_implies_Equation2 (G : Type*) [Magma G] (h : Equation41433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41435_implies_Equation2 (G : Type*) [Magma G] (h : Equation41435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41436_implies_Equation2 (G : Type*) [Magma G] (h : Equation41436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41437_implies_Equation2 (G : Type*) [Magma G] (h : Equation41437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41438_implies_Equation2 (G : Type*) [Magma G] (h : Equation41438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41439_implies_Equation2 (G : Type*) [Magma G] (h : Equation41439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41441_implies_Equation2 (G : Type*) [Magma G] (h : Equation41441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq36 eq15


@[equational_result]
theorem Equation41442_implies_Equation2 (G : Type*) [Magma G] (h : Equation41442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41443_implies_Equation2 (G : Type*) [Magma G] (h : Equation41443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X3) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X3) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation41444_implies_Equation2 (G : Type*) [Magma G] (h : Equation41444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X4) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41446_implies_Equation2 (G : Type*) [Magma G] (h : Equation41446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41447_implies_Equation2 (G : Type*) [Magma G] (h : Equation41447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41448_implies_Equation2 (G : Type*) [Magma G] (h : Equation41448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41449_implies_Equation2 (G : Type*) [Magma G] (h : Equation41449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41451_implies_Equation2 (G : Type*) [Magma G] (h : Equation41451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41452_implies_Equation2 (G : Type*) [Magma G] (h : Equation41452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41453_implies_Equation2 (G : Type*) [Magma G] (h : Equation41453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41454_implies_Equation2 (G : Type*) [Magma G] (h : Equation41454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41456_implies_Equation2 (G : Type*) [Magma G] (h : Equation41456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41457_implies_Equation2 (G : Type*) [Magma G] (h : Equation41457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41458_implies_Equation2 (G : Type*) [Magma G] (h : Equation41458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41459_implies_Equation2 (G : Type*) [Magma G] (h : Equation41459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41461_implies_Equation2 (G : Type*) [Magma G] (h : Equation41461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41462_implies_Equation2 (G : Type*) [Magma G] (h : Equation41462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41463_implies_Equation2 (G : Type*) [Magma G] (h : Equation41463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41464_implies_Equation2 (G : Type*) [Magma G] (h : Equation41464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41465_implies_Equation2 (G : Type*) [Magma G] (h : Equation41465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41467_implies_Equation2 (G : Type*) [Magma G] (h : Equation41467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq37 eq15


@[equational_result]
theorem Equation41468_implies_Equation2 (G : Type*) [Magma G] (h : Equation41468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41469_implies_Equation2 (G : Type*) [Magma G] (h : Equation41469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : ((((X0 ◇ X4) ◇ X4) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ X3) = X4 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq11 eq10
  have eq32 (X4 X5 : G) : (X4 ◇ X4) = X5 := superpose eq23 eq9
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq32 eq32
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq49 eq44


@[equational_result]
theorem Equation41470_implies_Equation2 (G : Type*) [Magma G] (h : Equation41470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : (((X0 ◇ X4) ◇ X5) ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41472_implies_Equation2 (G : Type*) [Magma G] (h : Equation41472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41473_implies_Equation2 (G : Type*) [Magma G] (h : Equation41473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41474_implies_Equation2 (G : Type*) [Magma G] (h : Equation41474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41475_implies_Equation2 (G : Type*) [Magma G] (h : Equation41475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41477_implies_Equation2 (G : Type*) [Magma G] (h : Equation41477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41478_implies_Equation2 (G : Type*) [Magma G] (h : Equation41478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41479_implies_Equation2 (G : Type*) [Magma G] (h : Equation41479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41480_implies_Equation2 (G : Type*) [Magma G] (h : Equation41480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41482_implies_Equation2 (G : Type*) [Magma G] (h : Equation41482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41483_implies_Equation2 (G : Type*) [Magma G] (h : Equation41483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41484_implies_Equation2 (G : Type*) [Magma G] (h : Equation41484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41485_implies_Equation2 (G : Type*) [Magma G] (h : Equation41485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41487_implies_Equation2 (G : Type*) [Magma G] (h : Equation41487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41488_implies_Equation2 (G : Type*) [Magma G] (h : Equation41488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41489_implies_Equation2 (G : Type*) [Magma G] (h : Equation41489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41490_implies_Equation2 (G : Type*) [Magma G] (h : Equation41490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41491_implies_Equation2 (G : Type*) [Magma G] (h : Equation41491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41493_implies_Equation2 (G : Type*) [Magma G] (h : Equation41493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq37 eq15


@[equational_result]
theorem Equation41494_implies_Equation2 (G : Type*) [Magma G] (h : Equation41494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X7) ◇ X2) = X7 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X4 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41495_implies_Equation2 (G : Type*) [Magma G] (h : Equation41495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : (((X0 ◇ X5) ◇ X6) ◇ X3) = X6 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X4 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation41496_implies_Equation2 (G : Type*) [Magma G] (h : Equation41496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41497_implies_Equation2 (G : Type*) [Magma G] (h : Equation41497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X6 X7 X8 X9 : G) : ((((X0 ◇ X6) ◇ X7) ◇ X8) ◇ X9) = X8 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation41499_implies_Equation2 (G : Type*) [Magma G] (h : Equation41499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41500_implies_Equation2 (G : Type*) [Magma G] (h : Equation41500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation41501_implies_Equation2 (G : Type*) [Magma G] (h : Equation41501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41502_implies_Equation2 (G : Type*) [Magma G] (h : Equation41502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41503_implies_Equation2 (G : Type*) [Magma G] (h : Equation41503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X1) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41505_implies_Equation2 (G : Type*) [Magma G] (h : Equation41505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41506_implies_Equation2 (G : Type*) [Magma G] (h : Equation41506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41507_implies_Equation2 (G : Type*) [Magma G] (h : Equation41507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41508_implies_Equation2 (G : Type*) [Magma G] (h : Equation41508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41509_implies_Equation2 (G : Type*) [Magma G] (h : Equation41509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X2) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41511_implies_Equation2 (G : Type*) [Magma G] (h : Equation41511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41512_implies_Equation2 (G : Type*) [Magma G] (h : Equation41512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41513_implies_Equation2 (G : Type*) [Magma G] (h : Equation41513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41514_implies_Equation2 (G : Type*) [Magma G] (h : Equation41514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41515_implies_Equation2 (G : Type*) [Magma G] (h : Equation41515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X3) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41517_implies_Equation2 (G : Type*) [Magma G] (h : Equation41517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41518_implies_Equation2 (G : Type*) [Magma G] (h : Equation41518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41519_implies_Equation2 (G : Type*) [Magma G] (h : Equation41519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41520_implies_Equation2 (G : Type*) [Magma G] (h : Equation41520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41521_implies_Equation2 (G : Type*) [Magma G] (h : Equation41521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41523_implies_Equation2 (G : Type*) [Magma G] (h : Equation41523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41524_implies_Equation2 (G : Type*) [Magma G] (h : Equation41524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41525_implies_Equation2 (G : Type*) [Magma G] (h : Equation41525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41526_implies_Equation2 (G : Type*) [Magma G] (h : Equation41526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41527_implies_Equation2 (G : Type*) [Magma G] (h : Equation41527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation41528_implies_Equation2 (G : Type*) [Magma G] (h : Equation41528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X5) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10544_implies_Equation2 (G : Type*) [Magma G] (h : Equation10544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))))) = X2 := superpose eq7 eq9
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0)) = X0 := superpose eq7 eq10
  have eq38 (X0 X1 : G) : (((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq11
  have eq64 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq38 eq38
  have eq67 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq38 eq25
  have eq68 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X2 := superpose eq38 eq7
  have eq106 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq38 eq68
  have eq119 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq106 eq67
  have eq213 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = ((X2 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq106 eq106
  have eq523 (X0 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = ((X2 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq38 eq213
  have eq527 (X0 X1 : G) : (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq119 eq213
  have eq2473 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose eq523 eq7
  have eq2525 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq2473
  have eq2526 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq2525 eq64
  have eq3068 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq2525 eq2526
  have eq3108 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq3068 eq527
  have eq3472 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq3068 eq3108
  have eq3473 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq7 eq3472
  have eq3474 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq3068 eq3473
  have eq3475 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq2525 eq3474
  have eq3476 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq2525 eq3475
  have eq3477 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq3476 eq2525
  have eq3479 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = X0 := superpose eq3477 eq7
  have eq3928 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq3477 eq3479
  have eq6358 (X0 X2 : G) : X0 = X2 := superpose eq3928 eq3928
  have eq6360 (X0 : G) : sK0 ≠ X0 := superpose eq6358 eq8
  subsumption eq6360 eq6358


@[equational_result]
theorem Equation23635_implies_Equation2 (G : Type*) [Magma G] (h : Equation23635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X0) = ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ X3) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X1) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) = (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X0)) ◇ ((((X2 ◇ X3) ◇ X1) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) ◇ ((X4 ◇ X5) ◇ (X1 ◇ X0))))) := superpose eq9 eq9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := superpose eq7 eq9
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X3 ◇ X0)) ◇ ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0)) := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)))) := superpose eq7 eq10
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0))) := superpose eq9 eq10
  have eq33 (X0 X1 X2 X3 : G) : (((((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2))) ◇ X3) ◇ X1) ◇ (((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq10 eq7
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq7 eq14
  have eq47 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) := superpose eq14 eq14
  have eq61 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ X2) = (((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ X3) ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) := superpose eq10 eq11
  have eq65 (X0 X1 X3 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X3) = ((((X1 ◇ (X3 ◇ X1)) ◇ X4) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X3)) := superpose eq10 eq11
  have eq77 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) = X3 := superpose eq11 eq9
  have eq253 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq7 eq77
  have eq291 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq77 eq77
  have eq295 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2))) = (X0 ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)))) := superpose eq77 eq10
  have eq304 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2)))) := superpose eq77 eq10
  have eq330 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq11 eq291
  have eq333 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)))) := superpose eq330 eq304
  have eq432 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1))) := superpose eq330 eq27
  have eq466 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1))) := superpose eq330 eq432
  have eq663 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) ◇ X4) = (((((((X1 ◇ (X3 ◇ X1)) ◇ X3) ◇ X0) ◇ (X4 ◇ (((X1 ◇ (X3 ◇ X1)) ◇ X3) ◇ X0))) ◇ X5) ◇ (((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) ◇ X4)) ◇ (((((X1 ◇ (X3 ◇ X1)) ◇ X3) ◇ X0) ◇ (X4 ◇ (((X1 ◇ (X3 ◇ X1)) ◇ X3) ◇ X0))) ◇ X4)) := superpose eq77 eq65
  have eq679 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq47 eq65
  have eq680 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq45 eq65
  have eq738 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq679 eq680
  have eq744 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq679 eq27
  have eq755 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq679 eq16
  have eq757 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq679 eq7
  have eq762 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq679 eq61
  have eq944 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq755 eq19
  have eq1142 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq757 eq27
  have eq1188 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq16 eq1142
  have eq1189 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq45 eq1188
  have eq1190 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq1189 eq679
  have eq1192 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq1190 eq738
  have eq1193 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq1190 eq744
  have eq1206 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq1190 eq757
  have eq1211 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq1190 eq762
  have eq1240 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq1190 eq944
  have eq1271 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq330 eq1240
  have eq1766 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq330 eq23
  have eq1840 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq330 eq1766
  have eq2219 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) = ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) ◇ X0)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) ◇ X0)))) := superpose eq23 eq33
  have eq2625 (X0 : G) : ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq1190 eq1840
  have eq2633 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq7 eq1840
  have eq2714 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq1840 eq9
  have eq2781 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq1840 eq2714
  have eq3253 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ X0) ◇ (X1 ◇ ((X4 ◇ X5) ◇ X0)))) ◇ (X1 ◇ ((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ X0) ◇ (X1 ◇ ((X4 ◇ X5) ◇ X0)))))) = (X1 ◇ ((X0 ◇ X1) ◇ ((((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ X0) ◇ (X1 ◇ ((X4 ◇ X5) ◇ X0)))) ◇ (X1 ◇ ((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ X0) ◇ (X1 ◇ ((X4 ◇ X5) ◇ X0)))))) ◇ (X0 ◇ X1)))) := superpose eq19 eq13
  have eq4068 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq1190 eq2781
  have eq4077 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq2781
  have eq4124 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ (X2 ◇ X0)) = (((X2 ◇ X0) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ (X2 ◇ X0))) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ (X2 ◇ X0))) := superpose eq14 eq2781
  have eq4168 (X0 X1 X2 : G) : ((X2 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2)) = (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2))) := superpose eq2781 eq1840
  have eq4240 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq1840 eq4068
  have eq4241 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq4240 eq2625
  have eq5059 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq1190 eq1192
  have eq8864 (X0 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) := superpose eq1190 eq253
  have eq8896 (X0 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq4168 eq8864
  have eq8897 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq4241 eq8896
  have eq8898 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq1840 eq8897
  have eq9226 (X0 : G) : ((X0 ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose eq8898 eq9
  have eq9290 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq5059 eq9226
  have eq9291 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq9290 eq1190
  have eq9294 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq9291 eq1193
  have eq9304 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq9291 eq1206
  have eq9306 (X0 X1 : G) : (((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq9291 eq1211
  have eq9319 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq9291 eq1271
  have eq9492 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq9294 eq9304
  have eq9497 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq9294 eq9306
  have eq9509 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9492 eq9319
  have eq9540 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9509 eq9291
  have eq9549 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq9509 eq9497
  have eq9595 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X1)) := superpose eq9549 eq466
  have eq9631 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) := superpose eq9540 eq9595
  have eq9632 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq9549 eq9631
  have eq9682 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (X0 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ X2))) := superpose eq9632 eq295
  have eq9698 (X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2)))) = X1 := superpose eq9632 eq333
  have eq9749 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) ◇ X4) = (((((X3 ◇ X0) ◇ (X4 ◇ (X3 ◇ X0))) ◇ X5) ◇ (((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) ◇ X4)) ◇ (((X3 ◇ X0) ◇ (X4 ◇ (X3 ◇ X0))) ◇ X4)) := superpose eq9632 eq663
  have eq9803 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ X1) = X1 := superpose eq9632 eq1840
  have eq9921 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq9632 eq4077
  have eq10414 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) = (X2 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ (((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) ◇ X0)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) ◇ X0)))) := superpose eq9632 eq2219
  have eq10424 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ (X2 ◇ X0)) = (((X2 ◇ X0) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq9632 eq4124
  have eq10815 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq9632 eq2633
  have eq11416 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := superpose eq9632 eq9682
  have eq11435 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ X0) ◇ (X1 ◇ ((X4 ◇ X5) ◇ X0)))))) = (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (((X4 ◇ X5) ◇ X0) ◇ (X1 ◇ ((X4 ◇ X5) ◇ X0)))))) ◇ (X0 ◇ X1)))) := superpose eq11416 eq3253
  have eq11452 (X1 X2 : G) : (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = X1 := superpose eq11416 eq9698
  have eq11484 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) ◇ X4) = (((((X3 ◇ X0) ◇ (X4 ◇ (X3 ◇ X0))) ◇ X5) ◇ (((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) ◇ X4)) ◇ X4) := superpose eq9632 eq9749
  have eq11485 (X0 X3 X4 X5 : G) : (X0 ◇ X4) = (((((X3 ◇ X0) ◇ (X4 ◇ (X3 ◇ X0))) ◇ X5) ◇ (X0 ◇ X4)) ◇ X4) := superpose eq9632 eq11484
  have eq11612 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq9632 eq9921
  have eq12193 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) = (X2 ◇ (X0 ◇ (((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) ◇ X0))) := superpose eq9632 eq10414
  have eq12194 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) = (X2 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) ◇ X0))) := superpose eq11416 eq12193
  have eq12588 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq11612 eq10815
  have eq12610 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X2 ◇ X0))) := superpose eq12588 eq10424
  have eq12615 (X0 X4 X5 : G) : (X0 ◇ X4) = (((X4 ◇ X5) ◇ (X0 ◇ X4)) ◇ X4) := superpose eq12588 eq11485
  have eq12620 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0))) := superpose eq12588 eq12194
  have eq12681 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) ◇ (X0 ◇ X1)))) := superpose eq12588 eq11435
  have eq13424 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ X0)) = (((X2 ◇ X0) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X0))) ◇ X2) := superpose eq12588 eq12610
  have eq13425 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = ((X0 ◇ X3) ◇ (X2 ◇ X0)) := superpose eq12588 eq13424
  have eq13455 (X0 X4 X5 : G) : (X0 ◇ X4) = (((X4 ◇ X5) ◇ X0) ◇ X4) := superpose eq13425 eq12615
  have eq13461 (X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq12588 eq12620
  have eq13462 (X2 X3 : G) : (X2 ◇ (X2 ◇ (X2 ◇ X3))) = X2 := superpose eq11452 eq13461
  have eq13625 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) := superpose eq12588 eq12681
  have eq13626 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X1 := superpose eq13462 eq13625
  have eq13627 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X3)) = X1 := superpose eq12588 eq13626
  have eq13628 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ X2) := superpose eq13627 eq13425
  have eq13663 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X1 := superpose eq13628 eq9803
  have eq13664 (X0 X4 X5 : G) : (X0 ◇ X4) = ((X4 ◇ X5) ◇ X4) := superpose eq13628 eq13455
  have eq13665 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq13663 eq13664
  have eq13668 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq13665 eq13627
  have eq14735 (X0 X1 : G) : X0 = X1 := superpose eq13665 eq13668
  have eq14749 (X0 : G) : sK0 ≠ X0 := superpose eq14735 eq8
  subsumption eq14749 eq14735


@[equational_result]
theorem Equation36790_implies_Equation2 (G : Type*) [Magma G] (h : Equation36790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) ◇ X3)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X0) := superpose eq7 eq10
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (((((((X1 ◇ X3) ◇ X0) ◇ (X1 ◇ X0)) ◇ X4) ◇ X1) ◇ X0) ◇ X2)) ◇ ((((((X1 ◇ X3) ◇ X0) ◇ (X1 ◇ X0)) ◇ X4) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq9
  have eq39 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3) := superpose eq10 eq14
  have eq123 (X0 X1 X3 : G) : (X0 ◇ X3) = ((((X1 ◇ X0) ◇ X1) ◇ (X3 ◇ (X0 ◇ X3))) ◇ X3) := superpose eq22 eq14
  have eq186 (X0 X1 X2 X3 : G) : ((((X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0))) ◇ X3) ◇ (X1 ◇ X0)) ◇ X1) = X0 := superpose eq7 eq123
  have eq785 (X0 X1 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq22 eq186
  have eq946 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)))) ◇ X1) := superpose eq785 eq785
  have eq965 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = (((((X1 ◇ X0) ◇ X1) ◇ (((((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)))) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq22 eq785
  have eq1672 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = X2 := superpose eq39 eq29
  have eq1767 (X0 X1 X2 X3 : G) : (((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ (X0 ◇ X3)) ◇ X0) = X3 := superpose eq22 eq1672
  have eq1860 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq1767
  have eq2071 (X0 X1 X3 : G) : ((X0 ◇ (X3 ◇ X1)) ◇ X3) = X1 := superpose eq7 eq1860
  have eq2479 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq22 eq2071
  have eq3115 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq2479 eq946
  have eq3117 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq2071 eq3115
  have eq3119 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq3117 eq785
  have eq3191 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = (((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq3119 eq965
  have eq3572 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq3119 eq3191
  have eq3573 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq3119 eq3572
  have eq3602 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq3573 eq7
  have eq4061 (X0 X2 : G) : X0 = X2 := superpose eq3602 eq3602
  have eq4136 (X0 : G) : sK0 ≠ X0 := superpose eq4061 eq8
  subsumption eq4136 eq4061


