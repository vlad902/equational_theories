import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation37043_implies_Equation2 (G : Type*) [Magma G] (h : Equation37043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37045_implies_Equation2 (G : Type*) [Magma G] (h : Equation37045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37046_implies_Equation2 (G : Type*) [Magma G] (h : Equation37046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37047_implies_Equation2 (G : Type*) [Magma G] (h : Equation37047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37048_implies_Equation2 (G : Type*) [Magma G] (h : Equation37048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37050_implies_Equation2 (G : Type*) [Magma G] (h : Equation37050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37051_implies_Equation2 (G : Type*) [Magma G] (h : Equation37051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37052_implies_Equation2 (G : Type*) [Magma G] (h : Equation37052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37053_implies_Equation2 (G : Type*) [Magma G] (h : Equation37053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37054_implies_Equation2 (G : Type*) [Magma G] (h : Equation37054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37056_implies_Equation2 (G : Type*) [Magma G] (h : Equation37056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation37057_implies_Equation2 (G : Type*) [Magma G] (h : Equation37057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37058_implies_Equation2 (G : Type*) [Magma G] (h : Equation37058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ (X3 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ (X3 ◇ X0))) ◇ X5) ◇ X0) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ (X4 ◇ X5)) ◇ X3) = X5 := superpose eq7 eq9
  have eq21 (X0 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X0) ◇ X5) = X4 := superpose eq12 eq11
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq52 eq30


@[equational_result]
theorem Equation37059_implies_Equation2 (G : Type*) [Magma G] (h : Equation37059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37061_implies_Equation2 (G : Type*) [Magma G] (h : Equation37061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37062_implies_Equation2 (G : Type*) [Magma G] (h : Equation37062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37063_implies_Equation2 (G : Type*) [Magma G] (h : Equation37063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37064_implies_Equation2 (G : Type*) [Magma G] (h : Equation37064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37066_implies_Equation2 (G : Type*) [Magma G] (h : Equation37066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37067_implies_Equation2 (G : Type*) [Magma G] (h : Equation37067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37068_implies_Equation2 (G : Type*) [Magma G] (h : Equation37068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37069_implies_Equation2 (G : Type*) [Magma G] (h : Equation37069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37071_implies_Equation2 (G : Type*) [Magma G] (h : Equation37071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37072_implies_Equation2 (G : Type*) [Magma G] (h : Equation37072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37073_implies_Equation2 (G : Type*) [Magma G] (h : Equation37073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37074_implies_Equation2 (G : Type*) [Magma G] (h : Equation37074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37076_implies_Equation2 (G : Type*) [Magma G] (h : Equation37076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37077_implies_Equation2 (G : Type*) [Magma G] (h : Equation37077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37078_implies_Equation2 (G : Type*) [Magma G] (h : Equation37078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37079_implies_Equation2 (G : Type*) [Magma G] (h : Equation37079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37080_implies_Equation2 (G : Type*) [Magma G] (h : Equation37080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37082_implies_Equation2 (G : Type*) [Magma G] (h : Equation37082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X5) ◇ (X5 ◇ X0))) ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X5 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq7 eq12
  have eq21 (X0 X1 X3 X5 : G) : ((X5 ◇ X0) ◇ X1) = X3 := superpose eq13 eq11
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq48 eq26


@[equational_result]
theorem Equation37083_implies_Equation2 (G : Type*) [Magma G] (h : Equation37083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37084_implies_Equation2 (G : Type*) [Magma G] (h : Equation37084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ X3) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq10
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq107 eq30


@[equational_result]
theorem Equation37085_implies_Equation2 (G : Type*) [Magma G] (h : Equation37085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37087_implies_Equation2 (G : Type*) [Magma G] (h : Equation37087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37088_implies_Equation2 (G : Type*) [Magma G] (h : Equation37088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37089_implies_Equation2 (G : Type*) [Magma G] (h : Equation37089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37090_implies_Equation2 (G : Type*) [Magma G] (h : Equation37090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37092_implies_Equation2 (G : Type*) [Magma G] (h : Equation37092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37093_implies_Equation2 (G : Type*) [Magma G] (h : Equation37093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37094_implies_Equation2 (G : Type*) [Magma G] (h : Equation37094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37095_implies_Equation2 (G : Type*) [Magma G] (h : Equation37095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37097_implies_Equation2 (G : Type*) [Magma G] (h : Equation37097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37098_implies_Equation2 (G : Type*) [Magma G] (h : Equation37098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37099_implies_Equation2 (G : Type*) [Magma G] (h : Equation37099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37100_implies_Equation2 (G : Type*) [Magma G] (h : Equation37100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37102_implies_Equation2 (G : Type*) [Magma G] (h : Equation37102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37103_implies_Equation2 (G : Type*) [Magma G] (h : Equation37103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37104_implies_Equation2 (G : Type*) [Magma G] (h : Equation37104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37105_implies_Equation2 (G : Type*) [Magma G] (h : Equation37105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37106_implies_Equation2 (G : Type*) [Magma G] (h : Equation37106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37108_implies_Equation2 (G : Type*) [Magma G] (h : Equation37108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq55 eq17


@[equational_result]
theorem Equation37109_implies_Equation2 (G : Type*) [Magma G] (h : Equation37109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37110_implies_Equation2 (G : Type*) [Magma G] (h : Equation37110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq43 eq16


@[equational_result]
theorem Equation37111_implies_Equation2 (G : Type*) [Magma G] (h : Equation37111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation37112_implies_Equation2 (G : Type*) [Magma G] (h : Equation37112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation37114_implies_Equation2 (G : Type*) [Magma G] (h : Equation37114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37115_implies_Equation2 (G : Type*) [Magma G] (h : Equation37115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37116_implies_Equation2 (G : Type*) [Magma G] (h : Equation37116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37117_implies_Equation2 (G : Type*) [Magma G] (h : Equation37117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37118_implies_Equation2 (G : Type*) [Magma G] (h : Equation37118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X1)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37120_implies_Equation2 (G : Type*) [Magma G] (h : Equation37120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37121_implies_Equation2 (G : Type*) [Magma G] (h : Equation37121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37122_implies_Equation2 (G : Type*) [Magma G] (h : Equation37122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37123_implies_Equation2 (G : Type*) [Magma G] (h : Equation37123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37124_implies_Equation2 (G : Type*) [Magma G] (h : Equation37124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37126_implies_Equation2 (G : Type*) [Magma G] (h : Equation37126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37127_implies_Equation2 (G : Type*) [Magma G] (h : Equation37127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37128_implies_Equation2 (G : Type*) [Magma G] (h : Equation37128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37129_implies_Equation2 (G : Type*) [Magma G] (h : Equation37129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37130_implies_Equation2 (G : Type*) [Magma G] (h : Equation37130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37132_implies_Equation2 (G : Type*) [Magma G] (h : Equation37132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37133_implies_Equation2 (G : Type*) [Magma G] (h : Equation37133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37134_implies_Equation2 (G : Type*) [Magma G] (h : Equation37134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37135_implies_Equation2 (G : Type*) [Magma G] (h : Equation37135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37136_implies_Equation2 (G : Type*) [Magma G] (h : Equation37136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37138_implies_Equation2 (G : Type*) [Magma G] (h : Equation37138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37139_implies_Equation2 (G : Type*) [Magma G] (h : Equation37139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37140_implies_Equation2 (G : Type*) [Magma G] (h : Equation37140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37141_implies_Equation2 (G : Type*) [Magma G] (h : Equation37141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37142_implies_Equation2 (G : Type*) [Magma G] (h : Equation37142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37143_implies_Equation2 (G : Type*) [Magma G] (h : Equation37143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37349_implies_Equation2 (G : Type*) [Magma G] (h : Equation37349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq38 eq24


@[equational_result]
theorem Equation37352_implies_Equation2 (G : Type*) [Magma G] (h : Equation37352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq65 eq14


@[equational_result]
theorem Equation37354_implies_Equation2 (G : Type*) [Magma G] (h : Equation37354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation37355_implies_Equation2 (G : Type*) [Magma G] (h : Equation37355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq9 eq9
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq23 eq14


@[equational_result]
theorem Equation37356_implies_Equation2 (G : Type*) [Magma G] (h : Equation37356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37359_implies_Equation2 (G : Type*) [Magma G] (h : Equation37359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq37 eq23


@[equational_result]
theorem Equation37362_implies_Equation2 (G : Type*) [Magma G] (h : Equation37362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq77 eq26


@[equational_result]
theorem Equation37364_implies_Equation2 (G : Type*) [Magma G] (h : Equation37364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation37366_implies_Equation2 (G : Type*) [Magma G] (h : Equation37366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37368_implies_Equation2 (G : Type*) [Magma G] (h : Equation37368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X3))) ◇ X1) = (X0 ◇ ((((((X0 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X3))) ◇ X1) ◇ ((((X0 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X3))) ◇ X1) ◇ X4)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X5))) ◇ (X1 ◇ X0))) := superpose eq10 eq10
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (((X2 ◇ (X2 ◇ X3)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0))) = X2 := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) ◇ X1) := superpose eq10 eq7
  have eq25 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X4))) ◇ X1)) := superpose eq11 eq10
  have eq32 (X0 X1 X3 : G) : (((X3 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3) = X0 := superpose eq7 eq18
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) := superpose eq18 eq18
  have eq72 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) := superpose eq10 eq32
  have eq319 (X0 X1 X3 : G) : (((X3 ◇ X1) ◇ X0) ◇ X3) = X0 := superpose eq7 eq72
  have eq334 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq17 eq72
  have eq341 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq72 eq32
  have eq384 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq319 eq334
  have eq392 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq341 eq384
  have eq393 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq392 eq36
  have eq439 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq341 eq393
  have eq440 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq319 eq439
  have eq441 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) := superpose eq440 eq25
  have eq444 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X3))) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X5)) ◇ (X1 ◇ X0))) := superpose eq440 eq13
  have eq488 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq440 eq441
  have eq489 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ X1) := superpose eq440 eq488
  have eq490 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq440 eq489
  have eq493 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X3))) ◇ X1) = X0 := superpose eq490 eq444
  have eq494 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X1) = X0 := superpose eq440 eq493
  have eq495 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X1) = X0 := superpose eq440 eq494
  have eq496 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq440 eq495
  have eq497 (X0 X3 : G) : X0 = X3 := superpose eq496 eq496
  have eq502 (X0 : G) : sK0 ≠ X0 := superpose eq497 eq8
  subsumption eq502 eq497


@[equational_result]
theorem Equation37369_implies_Equation2 (G : Type*) [Magma G] (h : Equation37369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation37370_implies_Equation2 (G : Type*) [Magma G] (h : Equation37370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq38 eq24


@[equational_result]
theorem Equation37372_implies_Equation2 (G : Type*) [Magma G] (h : Equation37372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X2) = (((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X3))) ◇ X2) ◇ X0)) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X1 ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = (((X2 ◇ X0) ◇ X2) ◇ X2) := superpose eq7 eq9
  have eq43 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) = X1 := superpose eq15 eq7
  have eq115 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq15 eq43
  have eq133 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq43 eq115
  have eq145 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq133 eq15
  have eq199 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) := superpose eq145 eq145
  have eq235 (X0 X1 X2 : G) : (X1 ◇ X2) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) := superpose eq145 eq43
  have eq250 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) = X1 := superpose eq43 eq199
  have eq263 (X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (X1 ◇ X2)) := superpose eq43 eq235
  have eq267 (X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) = X1 := superpose eq263 eq250
  have eq275 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) = X0 := superpose eq263 eq7
  have eq277 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X2))) = X1 := superpose eq263 eq10
  have eq365 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq267 eq277
  have eq366 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq365 eq43
  have eq374 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq366 eq275
  have eq387 (X0 X2 : G) : X0 = X2 := superpose eq374 eq374
  have eq389 (X0 : G) : sK0 ≠ X0 := superpose eq387 eq8
  subsumption eq389 eq387


@[equational_result]
theorem Equation37374_implies_Equation2 (G : Type*) [Magma G] (h : Equation37374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq65 eq14


@[equational_result]
theorem Equation37377_implies_Equation2 (G : Type*) [Magma G] (h : Equation37377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37378_implies_Equation2 (G : Type*) [Magma G] (h : Equation37378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37380_implies_Equation2 (G : Type*) [Magma G] (h : Equation37380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq67 eq20


@[equational_result]
theorem Equation37381_implies_Equation2 (G : Type*) [Magma G] (h : Equation37381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation37382_implies_Equation2 (G : Type*) [Magma G] (h : Equation37382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37383_implies_Equation2 (G : Type*) [Magma G] (h : Equation37383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37386_implies_Equation2 (G : Type*) [Magma G] (h : Equation37386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq36 eq22


@[equational_result]
theorem Equation37389_implies_Equation2 (G : Type*) [Magma G] (h : Equation37389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq78 eq26


@[equational_result]
theorem Equation37391_implies_Equation2 (G : Type*) [Magma G] (h : Equation37391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation37393_implies_Equation2 (G : Type*) [Magma G] (h : Equation37393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37396_implies_Equation2 (G : Type*) [Magma G] (h : Equation37396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq36 eq22


@[equational_result]
theorem Equation37399_implies_Equation2 (G : Type*) [Magma G] (h : Equation37399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq82 eq27


@[equational_result]
theorem Equation37401_implies_Equation2 (G : Type*) [Magma G] (h : Equation37401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq62 eq16


@[equational_result]
theorem Equation37403_implies_Equation2 (G : Type*) [Magma G] (h : Equation37403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37405_implies_Equation2 (G : Type*) [Magma G] (h : Equation37405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ (X3 ◇ X0)) ◇ X3) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0) = (((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0)) = X1 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) ◇ X0)) = (((X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) ◇ X0))) ◇ X1) := superpose eq7 eq10
  have eq48 (X0 X1 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) = X1 := superpose eq13 eq13
  have eq54 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) ◇ (X1 ◇ X0)) = X2 := superpose eq13 eq7
  have eq98 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ ((((((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) := superpose eq48 eq48
  have eq109 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq48 eq13
  have eq112 (X0 X1 : G) : (X1 ◇ X0) = (((((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq48 eq7
  have eq123 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq54 eq109
  have eq173 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq123 eq48
  have eq273 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) := superpose eq173 eq13
  have eq385 (X0 X1 X3 : G) : (((X0 ◇ (X3 ◇ X1)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq54
  have eq414 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) ◇ (((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0)) ◇ X3))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0))) := superpose eq54 eq13
  have eq537 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) := superpose eq13 eq385
  have eq553 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2)))) = X0 := superpose eq7 eq385
  have eq572 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq385 eq48
  have eq577 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ (X1 ◇ ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ X4))) ◇ X1) = ((X0 ◇ (((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ (X1 ◇ ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ X4))) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq385 eq10
  have eq610 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq537 eq112
  have eq614 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq572 eq273
  have eq615 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq614 eq572
  have eq616 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq173 eq615
  have eq617 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq616 eq610
  have eq736 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq13 eq616
  have eq792 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq616 eq48
  have eq798 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq173 eq792
  have eq1190 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq616 eq617
  have eq1288 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq553 eq1190
  have eq1290 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq1288 eq798
  have eq1293 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq1288 eq1290
  have eq1297 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (((X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4))) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1) := superpose eq1293 eq29
  have eq1312 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) ◇ X1) = ((X0 ◇ (((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq1293 eq577
  have eq1322 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0))) := superpose eq1293 eq414
  have eq1518 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ X1) := superpose eq1293 eq1297
  have eq1519 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq1293 eq1518
  have eq1520 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq537 eq1519
  have eq1556 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq1293 eq1312
  have eq1557 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) ◇ X1) := superpose eq1293 eq1556
  have eq1558 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) := superpose eq1520 eq1557
  have eq1559 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) = X0 := superpose eq1288 eq1558
  have eq1594 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0))) := superpose eq736 eq1322
  have eq1595 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq1293 eq1594
  have eq1596 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq1595 eq98
  have eq1597 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) := superpose eq1595 eq1596
  have eq1598 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq1597 eq48
  have eq1602 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X0 := superpose eq1598 eq1559
  have eq1616 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq1602 eq385
  have eq1666 (X0 X1 : G) : X0 = X1 := superpose eq173 eq1616
  have eq1700 (X0 : G) : sK0 ≠ X0 := superpose eq1666 eq8
  subsumption eq1700 eq1666


@[equational_result]
theorem Equation37407_implies_Equation2 (G : Type*) [Magma G] (h : Equation37407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ (X3 ◇ X0)) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq36 eq22


@[equational_result]
theorem Equation37409_implies_Equation2 (G : Type*) [Magma G] (h : Equation37409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) ◇ (X3 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X1 ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) = X1 := superpose eq10 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq10 eq7
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq9
  have eq39 (X0 X1 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) = X1 := superpose eq10 eq26
  have eq46 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = ((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ ((X0 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ (((X0 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X4)) := superpose eq10 eq17
  have eq83 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X2))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X2))) := superpose eq10 eq39
  have eq97 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) := superpose eq17 eq83
  have eq99 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := superpose eq97 eq18
  have eq114 (X0 X1 X2 X4 : G) : (X0 ◇ X2) = ((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) := superpose eq99 eq46
  have eq119 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq17 eq114
  have eq120 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X1 := superpose eq119 eq17
  have eq154 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq119 eq120
  have eq155 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq119 eq154
  have eq156 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq119 eq155
  have eq169 (X0 X2 : G) : X0 = X2 := superpose eq156 eq156
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq169 eq8
  subsumption eq174 eq169


@[equational_result]
theorem Equation37411_implies_Equation2 (G : Type*) [Magma G] (h : Equation37411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) ◇ (X3 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq9
  have eq27 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq85 eq27


@[equational_result]
theorem Equation37415_implies_Equation2 (G : Type*) [Magma G] (h : Equation37415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X3 := superpose eq7 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq29 eq16


@[equational_result]
theorem Equation37417_implies_Equation2 (G : Type*) [Magma G] (h : Equation37417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq83 eq20


@[equational_result]
theorem Equation37418_implies_Equation2 (G : Type*) [Magma G] (h : Equation37418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation37419_implies_Equation2 (G : Type*) [Magma G] (h : Equation37419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X4))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq18 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ (X2 ◇ X3))) ◇ ((X4 ◇ (X1 ◇ (X4 ◇ X5))) ◇ X6)) := superpose eq7 eq11
  have eq31 (X0 X1 X2 X3 X6 : G) : (X1 ◇ X0) = ((X2 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X1 ◇ X6)) := superpose eq16 eq18
  have eq32 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq16 eq31
  have eq35 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq32 eq16
  have eq38 (X0 X1 : G) : X0 = X1 := superpose eq32 eq35
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq48 eq38


@[equational_result]
theorem Equation37420_implies_Equation2 (G : Type*) [Magma G] (h : Equation37420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37422_implies_Equation2 (G : Type*) [Magma G] (h : Equation37422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X0))) ◇ X0)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X1))) ◇ X1) = (X0 ◇ ((((((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X1))) ◇ X1) ◇ (X4 ◇ (((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X3 ◇ X1))) ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X5 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X0))) := superpose eq10 eq10
  have eq30 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq10
  have eq40 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq30 eq10
  have eq96 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq9 eq17
  have eq97 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq17
  have eq114 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0) = (X0 ◇ X0) := superpose eq7 eq97
  have eq136 (X0 X1 X4 X5 : G) : (X1 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ (X4 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X5 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X0))) := superpose eq114 eq23
  have eq150 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq114 eq136
  have eq151 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq97 eq150
  have eq153 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq151 eq96
  have eq158 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq97 eq153
  have eq159 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq158 eq40
  have eq167 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq158 eq30
  have eq170 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq167 eq159
  have eq189 (X0 X2 : G) : X0 = X2 := superpose eq97 eq170
  have eq222 (X0 : G) : sK0 ≠ X0 := superpose eq189 eq8
  subsumption eq222 eq189


@[equational_result]
theorem Equation37423_implies_Equation2 (G : Type*) [Magma G] (h : Equation37423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation37424_implies_Equation2 (G : Type*) [Magma G] (h : Equation37424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq51 eq24


@[equational_result]
theorem Equation37426_implies_Equation2 (G : Type*) [Magma G] (h : Equation37426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X2 ◇ (X0 ◇ X3)) ◇ X2) := superpose eq9 eq9
  have eq33 (X0 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ X2) ◇ X4)) ◇ X3) = X0 := superpose eq9 eq12
  have eq35 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2)) ◇ X1) ◇ X1) = ((X4 ◇ X0) ◇ X4) := superpose eq7 eq12
  have eq67 (X0 X1 X2 X4 : G) : (X2 ◇ X1) = ((X4 ◇ X0) ◇ X4) := superpose eq33 eq35
  have eq155 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X2) = X3 := superpose eq67 eq9
  have eq204 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq33 eq155
  have eq253 (X0 X3 : G) : X0 = X3 := superpose eq7 eq204
  have eq466 (X0 : G) : sK0 ≠ X0 := superpose eq253 eq8
  subsumption eq466 eq253


@[equational_result]
theorem Equation37428_implies_Equation2 (G : Type*) [Magma G] (h : Equation37428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37431_implies_Equation2 (G : Type*) [Magma G] (h : Equation37431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation37432_implies_Equation2 (G : Type*) [Magma G] (h : Equation37432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37434_implies_Equation2 (G : Type*) [Magma G] (h : Equation37434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq47 eq30


@[equational_result]
theorem Equation37435_implies_Equation2 (G : Type*) [Magma G] (h : Equation37435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation37436_implies_Equation2 (G : Type*) [Magma G] (h : Equation37436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation37437_implies_Equation2 (G : Type*) [Magma G] (h : Equation37437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37439_implies_Equation2 (G : Type*) [Magma G] (h : Equation37439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1)))) ◇ X0) = (((X1 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1)))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0)) = X1 := superpose eq9 eq9
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq9 eq9
  have eq33 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) ◇ X3) ◇ X1) ◇ (((X1 ◇ X2) ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) ◇ X3))) = X1 := superpose eq10 eq9
  have eq44 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq16 eq7
  have eq48 (X0 X1 X2 : G) : (X0 ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq16 eq7
  have eq50 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X2))))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) = ((X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X4 ◇ (X1 ◇ (X0 ◇ X2))))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ (X0 ◇ X2)) := superpose eq16 eq10
  have eq66 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X2 ◇ X3) ◇ X0) ◇ (X0 ◇ X1))) = X2 := superpose eq16 eq14
  have eq69 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X0 ◇ X1)) := superpose eq9 eq14
  have eq70 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) ◇ X3) ◇ X1)) := superpose eq10 eq14
  have eq76 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq14 eq16
  have eq80 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq14 eq7
  have eq87 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq76 eq80
  have eq88 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) ◇ X3) ◇ X1) ◇ (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3))) = X1 := superpose eq87 eq33
  have eq95 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ X1)) := superpose eq87 eq70
  have eq97 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) = ((X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ (X0 ◇ X2)) := superpose eq87 eq50
  have eq116 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq87 eq69
  have eq120 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq76 eq88
  have eq121 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq87 eq120
  have eq122 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq76 eq121
  have eq123 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq122 eq66
  have eq124 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq122 eq48
  have eq132 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq76 eq95
  have eq133 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq124 eq132
  have eq135 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) = ((X0 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq87 eq97
  have eq136 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := superpose eq44 eq135
  have eq137 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2)) = X0 := superpose eq124 eq136
  have eq138 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq76 eq137
  have eq148 (X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = X2 := superpose eq138 eq9
  have eq163 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X1 := superpose eq148 eq116
  have eq164 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X1 := superpose eq163 eq133
  have eq166 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq164 eq123
  have eq175 (X0 X2 : G) : X0 = X2 := superpose eq166 eq166
  have eq183 (X0 : G) : sK0 ≠ X0 := superpose eq175 eq8
  subsumption eq183 eq175


@[equational_result]
theorem Equation37441_implies_Equation2 (G : Type*) [Magma G] (h : Equation37441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq50 eq23


@[equational_result]
theorem Equation37443_implies_Equation2 (G : Type*) [Magma G] (h : Equation37443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq27 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X2 ◇ X0)) = X1 := superpose eq10 eq7
  have eq29 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X0))))) ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X0))))) = X2 := superpose eq10 eq9
  have eq30 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X0)))) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq10 eq7
  have eq34 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X0) ◇ (X1 ◇ (X3 ◇ (X2 ◇ X0)))) := superpose eq9 eq30
  have eq35 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq34 eq29
  have eq38 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq27 eq35
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq38 eq38
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq83 eq45


@[equational_result]
theorem Equation37445_implies_Equation2 (G : Type*) [Magma G] (h : Equation37445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq57 eq39


@[equational_result]
theorem Equation37449_implies_Equation2 (G : Type*) [Magma G] (h : Equation37449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq73 eq15


@[equational_result]
theorem Equation37451_implies_Equation2 (G : Type*) [Magma G] (h : Equation37451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq49 eq31


@[equational_result]
theorem Equation37452_implies_Equation2 (G : Type*) [Magma G] (h : Equation37452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation37453_implies_Equation2 (G : Type*) [Magma G] (h : Equation37453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X5) ◇ X5) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X5) = X3 := superpose eq7 eq9
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation37454_implies_Equation2 (G : Type*) [Magma G] (h : Equation37454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37457_implies_Equation2 (G : Type*) [Magma G] (h : Equation37457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation37458_implies_Equation2 (G : Type*) [Magma G] (h : Equation37458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq51 eq24


@[equational_result]
theorem Equation37462_implies_Equation2 (G : Type*) [Magma G] (h : Equation37462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37465_implies_Equation2 (G : Type*) [Magma G] (h : Equation37465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq62 eq14


@[equational_result]
theorem Equation37466_implies_Equation2 (G : Type*) [Magma G] (h : Equation37466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37468_implies_Equation2 (G : Type*) [Magma G] (h : Equation37468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation37469_implies_Equation2 (G : Type*) [Magma G] (h : Equation37469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation37470_implies_Equation2 (G : Type*) [Magma G] (h : Equation37470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37471_implies_Equation2 (G : Type*) [Magma G] (h : Equation37471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37473_implies_Equation2 (G : Type*) [Magma G] (h : Equation37473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X5))) ◇ X0) = (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X5))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X5))) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)))) = X0 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X5))) ◇ X1) = (X0 ◇ ((((((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X5))) ◇ X1) ◇ (X6 ◇ X7)) ◇ ((X1 ◇ X0) ◇ (X8 ◇ X9))) ◇ (X1 ◇ X0))) := superpose eq11 eq11
  have eq40 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X4 ◇ X5) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X5) ◇ (X6 ◇ X7))) ◇ (X4 ◇ X5)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X5) ◇ (X6 ◇ X7))))) := superpose eq11 eq11
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq11
  have eq49 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq41
  have eq73 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X0) = (X0 ◇ ((((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X0) ◇ (X0 ◇ (X5 ◇ X6)))) := superpose eq7 eq12
  have eq74 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = (X0 ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) ◇ (X0 ◇ (X4 ◇ X5)))) := superpose eq9 eq12
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) = X0 := superpose eq12 eq12
  have eq85 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) = ((((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) ◇ (X0 ◇ X1)) ◇ (((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) ◇ (X0 ◇ X1))) := superpose eq9 eq12
  have eq99 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4))) = (X0 ◇ ((((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4))) ◇ (X5 ◇ X6)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X7 ◇ X8))) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq11
  have eq122 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X4 ◇ X5))) ◇ (X0 ◇ X0))) := superpose eq49 eq11
  have eq131 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X6))) ◇ (X0 ◇ (X3 ◇ X4))) = ((X0 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X6))) ◇ (X0 ◇ (X3 ◇ X4)))) ◇ (X0 ◇ X0)) := superpose eq41 eq10
  have eq132 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ X5))) ◇ (X0 ◇ X3)) = ((X0 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ X5))) ◇ (X0 ◇ X3))) ◇ (X0 ◇ X0)) := superpose eq49 eq10
  have eq173 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X5 ◇ (X6 ◇ X7)) ◇ X2) = ((X5 ◇ ((X5 ◇ (X6 ◇ X7)) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2) ◇ X5)) := superpose eq10 eq11
  have eq191 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X6))) ◇ (X0 ◇ (X3 ◇ X4))) = X0 := superpose eq83 eq131
  have eq192 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4))) = (X0 ◇ X0) := superpose eq191 eq99
  have eq193 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X4 ◇ X5) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X5) ◇ (X6 ◇ X7))) ◇ (X4 ◇ X5)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq192 eq40
  have eq198 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ X5))) ◇ (X0 ◇ X3)) = X0 := superpose eq83 eq132
  have eq203 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ X1) = (((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X4 ◇ X5))) ◇ X1) := superpose eq198 eq25
  have eq204 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq198 eq122
  have eq205 (X0 X1 X4 X5 : G) : (X4 ◇ X5) = (X4 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq198 eq193
  have eq208 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq203 eq11
  have eq211 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X0) = (X0 ◇ X0) := superpose eq204 eq73
  have eq212 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = (X0 ◇ X0) := superpose eq204 eq74
  have eq223 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq212 eq85
  have eq224 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X1) = ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) := superpose eq208 eq223
  have eq229 (X0 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ X3)) = X0 := superpose eq224 eq198
  have eq233 (X0 X4 X5 : G) : (X4 ◇ X5) = (X4 ◇ X0) := superpose eq229 eq205
  have eq238 (X2 X5 X6 X7 : G) : ((X5 ◇ (X6 ◇ X7)) ◇ X2) = ((X5 ◇ ((X5 ◇ (X6 ◇ X7)) ◇ X2)) ◇ ((X2 ◇ X2) ◇ X5)) := superpose eq211 eq173
  have eq239 (X2 X5 X6 X7 : G) : ((X5 ◇ (X6 ◇ X7)) ◇ X2) = ((X5 ◇ X5) ◇ ((X2 ◇ X2) ◇ X5)) := superpose eq204 eq238
  have eq251 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X0 := superpose eq41 eq233
  have eq294 (X2 X5 X6 X7 : G) : ((X5 ◇ (X6 ◇ X7)) ◇ X2) = X5 := superpose eq251 eq239
  have eq296 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq294 eq7
  have eq307 (X0 X1 : G) : X0 = X1 := superpose eq49 eq296
  have eq330 (X0 : G) : sK0 ≠ X0 := superpose eq307 eq8
  subsumption eq330 eq307


@[equational_result]
theorem Equation37474_implies_Equation2 (G : Type*) [Magma G] (h : Equation37474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq38 eq24


@[equational_result]
theorem Equation37475_implies_Equation2 (G : Type*) [Magma G] (h : Equation37475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq51 eq24


@[equational_result]
theorem Equation37476_implies_Equation2 (G : Type*) [Magma G] (h : Equation37476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X7 : G) : ((X0 ◇ X4) ◇ X7) = X4 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq51 eq24


@[equational_result]
theorem Equation37478_implies_Equation2 (G : Type*) [Magma G] (h : Equation37478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X5))) ◇ (X2 ◇ X3)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq40 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (((X2 ◇ X3) ◇ ((X1 ◇ (X4 ◇ X5)) ◇ (X6 ◇ X7))) ◇ (X2 ◇ X3)) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X8 ◇ X9)) := superpose eq10 eq10
  have eq41 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X6))) ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq10
  have eq58 (X0 X1 X8 X9 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X8 ◇ X9)) = X1 := superpose eq41 eq40
  have eq78 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X4 := superpose eq10 eq58
  have eq165 (X0 X4 : G) : X0 = X4 := superpose eq7 eq78
  have eq328 (X0 : G) : sK0 ≠ X0 := superpose eq165 eq8
  subsumption eq328 eq165


@[equational_result]
theorem Equation37479_implies_Equation2 (G : Type*) [Magma G] (h : Equation37479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ X5))) ◇ X2) = (((X1 ◇ X0) ◇ X1) ◇ X3) := superpose eq7 eq7
  have eq58 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (X2 ◇ X4)) = X1 := superpose eq10 eq7
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X1 := superpose eq58 eq58
  have eq116 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ X3) = X2 := superpose eq58 eq7
  have eq134 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq94 eq116
  have eq193 (X0 X4 : G) : X0 = X4 := superpose eq7 eq134
  have eq393 (X0 : G) : sK0 ≠ X0 := superpose eq193 eq8
  subsumption eq393 eq193


@[equational_result]
theorem Equation37480_implies_Equation2 (G : Type*) [Magma G] (h : Equation37480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq9 eq9
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq171 eq68


@[equational_result]
theorem Equation37481_implies_Equation2 (G : Type*) [Magma G] (h : Equation37481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X0 ◇ X6) = X1 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation37483_implies_Equation2 (G : Type*) [Magma G] (h : Equation37483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)))) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq12 eq12
  have eq56 (X0 X5 : G) : X0 = X5 := superpose eq7 eq20
  have eq190 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq190 eq56


@[equational_result]
theorem Equation37484_implies_Equation2 (G : Type*) [Magma G] (h : Equation37484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation37485_implies_Equation2 (G : Type*) [Magma G] (h : Equation37485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37486_implies_Equation2 (G : Type*) [Magma G] (h : Equation37486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X6 : G) : (X0 ◇ X6) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37488_implies_Equation2 (G : Type*) [Magma G] (h : Equation37488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))))) = X3 := superpose eq7 eq7
  have eq35 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq12
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq35
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq159 eq42


@[equational_result]
theorem Equation37489_implies_Equation2 (G : Type*) [Magma G] (h : Equation37489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37490_implies_Equation2 (G : Type*) [Magma G] (h : Equation37490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation37491_implies_Equation2 (G : Type*) [Magma G] (h : Equation37491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37493_implies_Equation2 (G : Type*) [Magma G] (h : Equation37493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq53 eq35


@[equational_result]
theorem Equation37494_implies_Equation2 (G : Type*) [Magma G] (h : Equation37494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37495_implies_Equation2 (G : Type*) [Magma G] (h : Equation37495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37496_implies_Equation2 (G : Type*) [Magma G] (h : Equation37496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X7 : G) : ((X0 ◇ X7) ◇ X7) = X4 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq29 eq17


@[equational_result]
theorem Equation37497_implies_Equation2 (G : Type*) [Magma G] (h : Equation37497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X8 : G) : (X0 ◇ X8) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37500_implies_Equation2 (G : Type*) [Magma G] (h : Equation37500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq10
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq37 eq23


@[equational_result]
theorem Equation37503_implies_Equation2 (G : Type*) [Magma G] (h : Equation37503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq10
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq78 eq26


@[equational_result]
theorem Equation37505_implies_Equation2 (G : Type*) [Magma G] (h : Equation37505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq40 eq15


@[equational_result]
theorem Equation37507_implies_Equation2 (G : Type*) [Magma G] (h : Equation37507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37510_implies_Equation2 (G : Type*) [Magma G] (h : Equation37510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq10
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq37 eq23


@[equational_result]
theorem Equation37513_implies_Equation2 (G : Type*) [Magma G] (h : Equation37513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq10
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq78 eq26


@[equational_result]
theorem Equation37515_implies_Equation2 (G : Type*) [Magma G] (h : Equation37515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq69 eq16


@[equational_result]
theorem Equation37517_implies_Equation2 (G : Type*) [Magma G] (h : Equation37517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37521_implies_Equation2 (G : Type*) [Magma G] (h : Equation37521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ X0) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq10
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq37 eq23


@[equational_result]
theorem Equation37523_implies_Equation2 (G : Type*) [Magma G] (h : Equation37523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4))) ◇ X2) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X5) := superpose eq9 eq9
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X1) = X0 := superpose eq7 eq9
  have eq32 (X0 X1 X5 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X5) = X1 := superpose eq22 eq21
  have eq34 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq10
  have eq54 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq22 eq34
  have eq59 (X0 X1 X5 : G) : (X0 ◇ X5) = X1 := superpose eq54 eq32
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq7 eq59
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq136 eq60


@[equational_result]
theorem Equation37525_implies_Equation2 (G : Type*) [Magma G] (h : Equation37525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq10
  have eq26 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq81 eq26


@[equational_result]
theorem Equation37529_implies_Equation2 (G : Type*) [Magma G] (h : Equation37529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X2) ◇ X0) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X3 := superpose eq7 eq10
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq77 eq16


@[equational_result]
theorem Equation37531_implies_Equation2 (G : Type*) [Magma G] (h : Equation37531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq81 eq20


@[equational_result]
theorem Equation37532_implies_Equation2 (G : Type*) [Magma G] (h : Equation37532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq75 eq12


@[equational_result]
theorem Equation37533_implies_Equation2 (G : Type*) [Magma G] (h : Equation37533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) = (((X1 ◇ (X1 ◇ X0)) ◇ X5) ◇ X5) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X4 ◇ (X4 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X5))) ◇ (X0 ◇ X6))) = X2 := superpose eq11 eq7
  have eq45 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X4) = X0 := superpose eq7 eq9
  have eq69 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq45 eq22
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq69
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq173 eq71


@[equational_result]
theorem Equation37534_implies_Equation2 (G : Type*) [Magma G] (h : Equation37534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37537_implies_Equation2 (G : Type*) [Magma G] (h : Equation37537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq36 eq22


@[equational_result]
theorem Equation37540_implies_Equation2 (G : Type*) [Magma G] (h : Equation37540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq39 eq27


@[equational_result]
theorem Equation37542_implies_Equation2 (G : Type*) [Magma G] (h : Equation37542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation37544_implies_Equation2 (G : Type*) [Magma G] (h : Equation37544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37547_implies_Equation2 (G : Type*) [Magma G] (h : Equation37547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = X0 := superpose eq13 eq7
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation37549_implies_Equation2 (G : Type*) [Magma G] (h : Equation37549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation37550_implies_Equation2 (G : Type*) [Magma G] (h : Equation37550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37552_implies_Equation2 (G : Type*) [Magma G] (h : Equation37552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37553_implies_Equation2 (G : Type*) [Magma G] (h : Equation37553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37554_implies_Equation2 (G : Type*) [Magma G] (h : Equation37554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37556_implies_Equation2 (G : Type*) [Magma G] (h : Equation37556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ X0)) ◇ X3) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)))) := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X0)) ◇ X3)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X0))) := superpose eq10 eq10
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq10 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)))) := superpose eq7 eq11
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X3)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := superpose eq7 eq14
  have eq20 (X0 X1 X2 : G) : (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) = (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))))) := superpose eq9 eq9
  have eq34 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) = X2 := superpose eq7 eq20
  have eq38 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ X3))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0))) = X1 := superpose eq7 eq34
  have eq48 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq34 eq10
  have eq53 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ X3))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = ((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq34 eq9
  have eq57 (X0 X1 X3 X4 : G) : ((((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3) ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3) ◇ X3)) ◇ X4) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3)) = X4 := superpose eq34 eq9
  have eq65 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0))) = X1 := superpose eq53 eq38
  have eq68 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X0))) := superpose eq10 eq15
  have eq84 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq15 eq34
  have eq93 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := superpose eq7 eq68
  have eq94 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) = (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)))) := superpose eq93 eq21
  have eq95 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq34 eq84
  have eq99 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (((((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)))) := superpose eq95 eq94
  have eq101 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := superpose eq95 eq17
  have eq108 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq95 eq18
  have eq118 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq95 eq48
  have eq124 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0))) = X1 := superpose eq95 eq65
  have eq134 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) := superpose eq95 eq99
  have eq136 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq95 eq101
  have eq138 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq136 eq134
  have eq141 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq118 eq138
  have eq142 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq95 eq141
  have eq144 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq142 eq108
  have eq148 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq142 eq144
  have eq149 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq142 eq148
  have eq150 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq118 eq149
  have eq153 (X0 X1 X3 X4 : G) : (((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3) ◇ X4) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X3)) = X4 := superpose eq150 eq57
  have eq167 (X0 X1 X3 X4 : G) : ((((X1 ◇ X0) ◇ X3) ◇ X4) ◇ ((X1 ◇ X0) ◇ X3)) = X4 := superpose eq150 eq153
  have eq184 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq167 eq124
  have eq213 (X0 X2 : G) : X0 = X2 := superpose eq184 eq184
  have eq239 (X0 : G) : sK0 ≠ X0 := superpose eq213 eq8
  subsumption eq239 eq213


@[equational_result]
theorem Equation37558_implies_Equation2 (G : Type*) [Magma G] (h : Equation37558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0) ◇ X0)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X3) = X0 := superpose eq13 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation37560_implies_Equation2 (G : Type*) [Magma G] (h : Equation37560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37561_implies_Equation2 (G : Type*) [Magma G] (h : Equation37561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37562_implies_Equation2 (G : Type*) [Magma G] (h : Equation37562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37564_implies_Equation2 (G : Type*) [Magma G] (h : Equation37564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37565_implies_Equation2 (G : Type*) [Magma G] (h : Equation37565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37566_implies_Equation2 (G : Type*) [Magma G] (h : Equation37566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37568_implies_Equation2 (G : Type*) [Magma G] (h : Equation37568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37569_implies_Equation2 (G : Type*) [Magma G] (h : Equation37569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37570_implies_Equation2 (G : Type*) [Magma G] (h : Equation37570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37571_implies_Equation2 (G : Type*) [Magma G] (h : Equation37571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37573_implies_Equation2 (G : Type*) [Magma G] (h : Equation37573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X3) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq9 eq9
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq9 eq13
  have eq37 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)) := superpose eq13 eq13
  have eq40 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq13 eq7
  have eq48 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X2 ◇ X3) ◇ X2) := superpose eq9 eq37
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq12 eq12
  have eq83 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)) := superpose eq13 eq40
  have eq103 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) := superpose eq40 eq9
  have eq105 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq83
  have eq123 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq105 eq57
  have eq128 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq103
  have eq130 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq128 eq123
  have eq132 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq128 eq33
  have eq133 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq132 eq130
  have eq135 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X0 := superpose eq133 eq7
  have eq140 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq133 eq105
  have eq146 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq140 eq48
  have eq157 (X0 X1 : G) : X0 = X1 := superpose eq135 eq146
  have eq199 (X0 : G) : sK0 ≠ X0 := superpose eq157 eq8
  subsumption eq199 eq157


@[equational_result]
theorem Equation37575_implies_Equation2 (G : Type*) [Magma G] (h : Equation37575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq10
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq61 eq23


@[equational_result]
theorem Equation37577_implies_Equation2 (G : Type*) [Magma G] (h : Equation37577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation37579_implies_Equation2 (G : Type*) [Magma G] (h : Equation37579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X5) = X4 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq72 eq20


@[equational_result]
theorem Equation37583_implies_Equation2 (G : Type*) [Magma G] (h : Equation37583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) ◇ X0) ◇ X3) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ X5) = X4 := superpose eq7 eq10
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq76 eq16


@[equational_result]
theorem Equation37585_implies_Equation2 (G : Type*) [Magma G] (h : Equation37585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X5) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation37586_implies_Equation2 (G : Type*) [Magma G] (h : Equation37586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation37587_implies_Equation2 (G : Type*) [Magma G] (h : Equation37587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation37588_implies_Equation2 (G : Type*) [Magma G] (h : Equation37588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37590_implies_Equation2 (G : Type*) [Magma G] (h : Equation37590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X3) ◇ X1) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq9 eq14
  have eq35 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq14 eq7
  have eq63 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)) := superpose eq14 eq35
  have eq82 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) := superpose eq35 eq9
  have eq83 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq63
  have eq94 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq82
  have eq96 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq94 eq29
  have eq141 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq83 eq83
  have eq144 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq83
  have eq161 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq96 eq141
  have eq166 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) = X0 := superpose eq161 eq7
  have eq184 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq144 eq166
  have eq195 (X0 X2 : G) : X0 = X2 := superpose eq184 eq184
  have eq197 (X0 : G) : sK0 ≠ X0 := superpose eq195 eq8
  subsumption eq197 eq195


@[equational_result]
theorem Equation37592_implies_Equation2 (G : Type*) [Magma G] (h : Equation37592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X3) = X0 := superpose eq13 eq7
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq30 eq23


@[equational_result]
theorem Equation37594_implies_Equation2 (G : Type*) [Magma G] (h : Equation37594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37595_implies_Equation2 (G : Type*) [Magma G] (h : Equation37595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37596_implies_Equation2 (G : Type*) [Magma G] (h : Equation37596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37598_implies_Equation2 (G : Type*) [Magma G] (h : Equation37598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37599_implies_Equation2 (G : Type*) [Magma G] (h : Equation37599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37600_implies_Equation2 (G : Type*) [Magma G] (h : Equation37600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37602_implies_Equation2 (G : Type*) [Magma G] (h : Equation37602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37603_implies_Equation2 (G : Type*) [Magma G] (h : Equation37603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37604_implies_Equation2 (G : Type*) [Magma G] (h : Equation37604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37605_implies_Equation2 (G : Type*) [Magma G] (h : Equation37605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37609_implies_Equation2 (G : Type*) [Magma G] (h : Equation37609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0) ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X3) = X0 := superpose eq13 eq7
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq30 eq23


@[equational_result]
theorem Equation37611_implies_Equation2 (G : Type*) [Magma G] (h : Equation37611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37612_implies_Equation2 (G : Type*) [Magma G] (h : Equation37612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37613_implies_Equation2 (G : Type*) [Magma G] (h : Equation37613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37615_implies_Equation2 (G : Type*) [Magma G] (h : Equation37615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37616_implies_Equation2 (G : Type*) [Magma G] (h : Equation37616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37617_implies_Equation2 (G : Type*) [Magma G] (h : Equation37617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37619_implies_Equation2 (G : Type*) [Magma G] (h : Equation37619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37620_implies_Equation2 (G : Type*) [Magma G] (h : Equation37620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37621_implies_Equation2 (G : Type*) [Magma G] (h : Equation37621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37622_implies_Equation2 (G : Type*) [Magma G] (h : Equation37622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37624_implies_Equation2 (G : Type*) [Magma G] (h : Equation37624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ X0) ◇ X0) ◇ X5) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ X0)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq9
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) = (((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ X0) ◇ X5) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ X0)) := superpose eq11 eq15
  have eq48 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq15 eq9
  have eq56 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) = (((X3 ◇ X4) ◇ X5) ◇ (X3 ◇ X4)) := superpose eq7 eq45
  have eq80 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ X0) ◇ X5) ◇ X5) ◇ X6) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ X0) ◇ X5)) = X6 := superpose eq11 eq10
  have eq101 (X3 X4 X5 X6 : G) : (((((X3 ◇ X4) ◇ X5) ◇ X5) ◇ X6) ◇ ((X3 ◇ X4) ◇ X5)) = X6 := superpose eq7 eq80
  have eq107 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ X0) = (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ X0)) := superpose eq11 eq48
  have eq108 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0)) := superpose eq15 eq48
  have eq132 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) ◇ X4) ◇ (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) ◇ X4) ◇ X5)) = ((((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) ◇ X4) ◇ (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) ◇ X4) ◇ X5)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4)) := superpose eq48 eq10
  have eq133 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)) := superpose eq7 eq107
  have eq135 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X2 := superpose eq9 eq108
  have eq166 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) ◇ X4) ◇ X5) = (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) ◇ X4) ◇ (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) ◇ X4) ◇ X5)) := superpose eq101 eq132
  have eq167 (X4 X5 : G) : (X4 ◇ X5) = (X4 ◇ (X4 ◇ X5)) := superpose eq135 eq166
  have eq177 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X5) ◇ (X3 ◇ X4)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) := superpose eq167 eq56
  have eq178 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)) := superpose eq167 eq133
  have eq184 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq167 eq15
  have eq193 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) = X3 := superpose eq184 eq177
  have eq195 (X3 X4 : G) : (X3 ◇ X4) = X3 := superpose eq193 eq178
  have eq201 (X3 X4 X5 X6 : G) : ((((X3 ◇ X4) ◇ X5) ◇ X6) ◇ ((X3 ◇ X4) ◇ X5)) = X6 := superpose eq195 eq101
  have eq217 (X3 X4 X6 : G) : (((X3 ◇ X4) ◇ X6) ◇ (X3 ◇ X4)) = X6 := superpose eq195 eq201
  have eq218 (X3 X6 : G) : ((X3 ◇ X6) ◇ X3) = X6 := superpose eq195 eq217
  have eq219 (X3 X6 : G) : (X3 ◇ X3) = X6 := superpose eq195 eq218
  have eq222 (X0 X2 : G) : X0 = X2 := superpose eq219 eq219
  have eq224 (X0 : G) : sK0 ≠ X0 := superpose eq222 eq8
  subsumption eq224 eq222


@[equational_result]
theorem Equation37625_implies_Equation2 (G : Type*) [Magma G] (h : Equation37625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X4)) ◇ X3) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq11 eq11
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq149 eq54


@[equational_result]
theorem Equation37626_implies_Equation2 (G : Type*) [Magma G] (h : Equation37626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X0) ◇ X0) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq9 eq10
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X3) = X0 := superpose eq12 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq13 eq13
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation37627_implies_Equation2 (G : Type*) [Magma G] (h : Equation37627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X6 X7 : G) : (((((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X4) = X0 := superpose eq13 eq7
  have eq23 (X0 X5 : G) : X0 = X5 := superpose eq14 eq14
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq30 eq23


@[equational_result]
theorem Equation37629_implies_Equation2 (G : Type*) [Magma G] (h : Equation37629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37630_implies_Equation2 (G : Type*) [Magma G] (h : Equation37630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37631_implies_Equation2 (G : Type*) [Magma G] (h : Equation37631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37632_implies_Equation2 (G : Type*) [Magma G] (h : Equation37632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37634_implies_Equation2 (G : Type*) [Magma G] (h : Equation37634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37635_implies_Equation2 (G : Type*) [Magma G] (h : Equation37635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37636_implies_Equation2 (G : Type*) [Magma G] (h : Equation37636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37637_implies_Equation2 (G : Type*) [Magma G] (h : Equation37637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37639_implies_Equation2 (G : Type*) [Magma G] (h : Equation37639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37640_implies_Equation2 (G : Type*) [Magma G] (h : Equation37640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37641_implies_Equation2 (G : Type*) [Magma G] (h : Equation37641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37642_implies_Equation2 (G : Type*) [Magma G] (h : Equation37642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37644_implies_Equation2 (G : Type*) [Magma G] (h : Equation37644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37645_implies_Equation2 (G : Type*) [Magma G] (h : Equation37645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37646_implies_Equation2 (G : Type*) [Magma G] (h : Equation37646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37647_implies_Equation2 (G : Type*) [Magma G] (h : Equation37647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37648_implies_Equation2 (G : Type*) [Magma G] (h : Equation37648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37650_implies_Equation2 (G : Type*) [Magma G] (h : Equation37650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X1 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq15 eq14
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq9 eq21
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq62 eq30


@[equational_result]
theorem Equation37651_implies_Equation2 (G : Type*) [Magma G] (h : Equation37651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation37652_implies_Equation2 (G : Type*) [Magma G] (h : Equation37652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37654_implies_Equation2 (G : Type*) [Magma G] (h : Equation37654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq42 eq15


@[equational_result]
theorem Equation37656_implies_Equation2 (G : Type*) [Magma G] (h : Equation37656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation37659_implies_Equation2 (G : Type*) [Magma G] (h : Equation37659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation37660_implies_Equation2 (G : Type*) [Magma G] (h : Equation37660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37662_implies_Equation2 (G : Type*) [Magma G] (h : Equation37662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation37663_implies_Equation2 (G : Type*) [Magma G] (h : Equation37663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation37664_implies_Equation2 (G : Type*) [Magma G] (h : Equation37664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq33 eq15


@[equational_result]
theorem Equation37665_implies_Equation2 (G : Type*) [Magma G] (h : Equation37665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37667_implies_Equation2 (G : Type*) [Magma G] (h : Equation37667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X1 := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq14 eq13
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq10 eq19
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq67 eq35


@[equational_result]
theorem Equation37669_implies_Equation2 (G : Type*) [Magma G] (h : Equation37669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation37671_implies_Equation2 (G : Type*) [Magma G] (h : Equation37671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq65 eq15


@[equational_result]
theorem Equation37673_implies_Equation2 (G : Type*) [Magma G] (h : Equation37673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X1) ◇ X5) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq70 eq18


@[equational_result]
theorem Equation37677_implies_Equation2 (G : Type*) [Magma G] (h : Equation37677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation37679_implies_Equation2 (G : Type*) [Magma G] (h : Equation37679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation37680_implies_Equation2 (G : Type*) [Magma G] (h : Equation37680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq74 eq12


@[equational_result]
theorem Equation37681_implies_Equation2 (G : Type*) [Magma G] (h : Equation37681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation37682_implies_Equation2 (G : Type*) [Magma G] (h : Equation37682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37685_implies_Equation2 (G : Type*) [Magma G] (h : Equation37685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation37686_implies_Equation2 (G : Type*) [Magma G] (h : Equation37686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37688_implies_Equation2 (G : Type*) [Magma G] (h : Equation37688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X2) = (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) = (((X4 ◇ (X1 ◇ X2)) ◇ X4) ◇ X4) := superpose eq9 eq9
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X4 ◇ (X3 ◇ X4))) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) = (((X5 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) ◇ X5) ◇ X5) := superpose eq9 eq9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ ((X2 ◇ X3) ◇ X4))) ◇ X3) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X1) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X1) = X2 := superpose eq25 eq24
  have eq51 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) = (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq25 eq25
  have eq53 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq25
  have eq110 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = X0 := superpose eq25 eq53
  have eq111 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X0 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq53 eq53
  have eq164 (X0 X1 X4 : G) : (((X4 ◇ X0) ◇ X4) ◇ X4) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq17
  have eq465 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X2 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X3))) := superpose eq164 eq110
  have eq466 (X0 X1 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) = X1 := superpose eq164 eq110
  have eq778 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X0)) ◇ X1) ◇ X1) = X0 := superpose eq466 eq7
  have eq2083 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((((X4 ◇ X1) ◇ X4) ◇ X4) ◇ X3)) = ((((X2 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ X0) := superpose eq465 eq33
  have eq2102 (X1 X3 X4 : G) : (X3 ◇ ((((X4 ◇ X1) ◇ X4) ◇ X4) ◇ X3)) = X1 := superpose eq33 eq2083
  have eq2225 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = (X3 ◇ ((((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) ◇ X0) ◇ X3)) := superpose eq111 eq2102
  have eq2267 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) = X1 := superpose eq2102 eq33
  have eq2284 (X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = (X3 ◇ (X2 ◇ X3)) := superpose eq7 eq2225
  have eq2591 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq2284 eq2284
  have eq2631 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq2284 eq7
  have eq2646 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := superpose eq2284 eq53
  have eq3483 (X0 X1 X2 X3 : G) : (X0 ◇ (((X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X3) ◇ X3)) = X1 := superpose eq7 eq2267
  have eq3843 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X1) = X3 := superpose eq2591 eq25
  have eq4117 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq2631 eq110
  have eq4525 (X0 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq4117 eq25
  have eq4953 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq4525
  have eq4954 (X0 X1 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X1) = X1 := superpose eq164 eq4525
  have eq4975 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq4954 eq778
  have eq4983 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X1 := superpose eq4975 eq3483
  have eq6538 (X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X1) = X3 := superpose eq4983 eq3843
  have eq6542 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq6538 eq4953
  have eq6543 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X2))) = X1 := superpose eq6538 eq2646
  have eq6709 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq6543 eq6542
  have eq6714 (X0 X2 X3 X4 X5 : G) : ((((X3 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X4 ◇ (X3 ◇ X4))) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) = (((X5 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X5) ◇ X5) := superpose eq6709 eq19
  have eq6719 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) = ((X1 ◇ X0) ◇ X1) := superpose eq6709 eq51
  have eq7161 (X0 X2 X3 X4 : G) : ((((X3 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X4 ◇ (X3 ◇ X4))) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ X2) ◇ X0) := superpose eq4975 eq6714
  have eq7162 (X0 X2 X3 : G) : ((((X3 ◇ (X0 ◇ X2)) ◇ X3) ◇ X3) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ X2) ◇ X0) := superpose eq6709 eq7161
  have eq7163 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = ((X0 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) := superpose eq4975 eq7162
  have eq7167 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq6709 eq6719
  have eq7168 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq6709 eq7167
  have eq7170 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7168 eq4975
  have eq7173 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X3)) = X2 := superpose eq7168 eq7163
  have eq7182 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) = X2 := superpose eq7170 eq7173
  have eq7183 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7170 eq7182
  have eq7184 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7170 eq7183
  have eq7185 (X0 X3 : G) : X0 = X3 := superpose eq7184 eq7184
  have eq7187 (X0 : G) : sK0 ≠ X0 := superpose eq7185 eq8
  subsumption eq7187 eq7185


@[equational_result]
theorem Equation37690_implies_Equation2 (G : Type*) [Magma G] (h : Equation37690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation37693_implies_Equation2 (G : Type*) [Magma G] (h : Equation37693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq63 eq14


@[equational_result]
theorem Equation37694_implies_Equation2 (G : Type*) [Magma G] (h : Equation37694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37696_implies_Equation2 (G : Type*) [Magma G] (h : Equation37696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq80 eq19


@[equational_result]
theorem Equation37697_implies_Equation2 (G : Type*) [Magma G] (h : Equation37697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation37698_implies_Equation2 (G : Type*) [Magma G] (h : Equation37698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37699_implies_Equation2 (G : Type*) [Magma G] (h : Equation37699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37701_implies_Equation2 (G : Type*) [Magma G] (h : Equation37701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = X1 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq16 eq15
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq10 eq23
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq76 eq40


@[equational_result]
theorem Equation37702_implies_Equation2 (G : Type*) [Magma G] (h : Equation37702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq38 eq24


@[equational_result]
theorem Equation37703_implies_Equation2 (G : Type*) [Magma G] (h : Equation37703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37704_implies_Equation2 (G : Type*) [Magma G] (h : Equation37704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X7 : G) : (((X1 ◇ X0) ◇ X5) ◇ X7) = X5 := superpose eq7 eq7
  have eq11 (X0 X5 X7 : G) : ((X0 ◇ X5) ◇ X7) = X5 := superpose eq7 eq7
  have eq15 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37706_implies_Equation2 (G : Type*) [Magma G] (h : Equation37706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation37707_implies_Equation2 (G : Type*) [Magma G] (h : Equation37707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X4 ◇ (X0 ◇ X5))) ◇ X3) = (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X2) := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X8 : G) : ((X3 ◇ (X4 ◇ ((X2 ◇ X5) ◇ X6))) ◇ X3) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X8) := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) ◇ X1) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ (X6 ◇ (X2 ◇ X7)))) ◇ X3) = X4 := superpose eq9 eq7
  have eq41 (X0 X1 X2 X8 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X8) = X2 := superpose eq29 eq28
  have eq44 (X2 X3 X4 : G) : (X2 ◇ X3) = X4 := superpose eq41 eq34
  have eq81 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq193 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq193 eq81


@[equational_result]
theorem Equation37708_implies_Equation2 (G : Type*) [Magma G] (h : Equation37708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X1) ◇ X5) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq83 eq17


@[equational_result]
theorem Equation37709_implies_Equation2 (G : Type*) [Magma G] (h : Equation37709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X6 : G) : (X0 ◇ X6) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation37711_implies_Equation2 (G : Type*) [Magma G] (h : Equation37711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X4 ◇ (X0 ◇ X5))) ◇ X4)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X5))) ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)))) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) ◇ X0) = X2 := superpose eq12 eq12
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq21 eq11
  have eq27 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X1) = X2 := superpose eq25 eq10
  have eq37 (X1 X2 X4 : G) : (X4 ◇ X1) = X2 := superpose eq25 eq27
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation37712_implies_Equation2 (G : Type*) [Magma G] (h : Equation37712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation37713_implies_Equation2 (G : Type*) [Magma G] (h : Equation37713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37714_implies_Equation2 (G : Type*) [Magma G] (h : Equation37714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37716_implies_Equation2 (G : Type*) [Magma G] (h : Equation37716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq56 eq19


@[equational_result]
theorem Equation37717_implies_Equation2 (G : Type*) [Magma G] (h : Equation37717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37718_implies_Equation2 (G : Type*) [Magma G] (h : Equation37718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation37719_implies_Equation2 (G : Type*) [Magma G] (h : Equation37719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37721_implies_Equation2 (G : Type*) [Magma G] (h : Equation37721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (((X1 ◇ X0) ◇ X7) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq64 eq19


@[equational_result]
theorem Equation37722_implies_Equation2 (G : Type*) [Magma G] (h : Equation37722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37723_implies_Equation2 (G : Type*) [Magma G] (h : Equation37723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37724_implies_Equation2 (G : Type*) [Magma G] (h : Equation37724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X7 : G) : ((X0 ◇ X7) ◇ X7) = X5 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq35 eq17


@[equational_result]
theorem Equation37725_implies_Equation2 (G : Type*) [Magma G] (h : Equation37725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X8 : G) : (X0 ◇ X8) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37727_implies_Equation2 (G : Type*) [Magma G] (h : Equation37727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X1 := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq14 eq13
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq10 eq19
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq61 eq29


@[equational_result]
theorem Equation37729_implies_Equation2 (G : Type*) [Magma G] (h : Equation37729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X3 ◇ X0)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq36 eq22


@[equational_result]
theorem Equation37731_implies_Equation2 (G : Type*) [Magma G] (h : Equation37731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation37733_implies_Equation2 (G : Type*) [Magma G] (h : Equation37733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X1) ◇ X5) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq71 eq19


@[equational_result]
theorem Equation37737_implies_Equation2 (G : Type*) [Magma G] (h : Equation37737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) ◇ (X3 ◇ X0)) ◇ X3) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ X5) = X4 := superpose eq7 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq29 eq16


@[equational_result]
theorem Equation37739_implies_Equation2 (G : Type*) [Magma G] (h : Equation37739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq60 eq18


@[equational_result]
theorem Equation37740_implies_Equation2 (G : Type*) [Magma G] (h : Equation37740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation37741_implies_Equation2 (G : Type*) [Magma G] (h : Equation37741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation37742_implies_Equation2 (G : Type*) [Magma G] (h : Equation37742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37744_implies_Equation2 (G : Type*) [Magma G] (h : Equation37744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = X1 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq14 eq13
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq9 eq18
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq30 eq21


@[equational_result]
theorem Equation37746_implies_Equation2 (G : Type*) [Magma G] (h : Equation37746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X3 ◇ X0)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ X3) = X0 := superpose eq13 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation37748_implies_Equation2 (G : Type*) [Magma G] (h : Equation37748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37749_implies_Equation2 (G : Type*) [Magma G] (h : Equation37749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37750_implies_Equation2 (G : Type*) [Magma G] (h : Equation37750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37752_implies_Equation2 (G : Type*) [Magma G] (h : Equation37752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37753_implies_Equation2 (G : Type*) [Magma G] (h : Equation37753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37754_implies_Equation2 (G : Type*) [Magma G] (h : Equation37754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37756_implies_Equation2 (G : Type*) [Magma G] (h : Equation37756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37757_implies_Equation2 (G : Type*) [Magma G] (h : Equation37757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37758_implies_Equation2 (G : Type*) [Magma G] (h : Equation37758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37759_implies_Equation2 (G : Type*) [Magma G] (h : Equation37759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37763_implies_Equation2 (G : Type*) [Magma G] (h : Equation37763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X0) ◇ (X3 ◇ X0)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X3) = X0 := superpose eq13 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation37765_implies_Equation2 (G : Type*) [Magma G] (h : Equation37765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37766_implies_Equation2 (G : Type*) [Magma G] (h : Equation37766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37767_implies_Equation2 (G : Type*) [Magma G] (h : Equation37767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37769_implies_Equation2 (G : Type*) [Magma G] (h : Equation37769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37770_implies_Equation2 (G : Type*) [Magma G] (h : Equation37770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37771_implies_Equation2 (G : Type*) [Magma G] (h : Equation37771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37773_implies_Equation2 (G : Type*) [Magma G] (h : Equation37773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37774_implies_Equation2 (G : Type*) [Magma G] (h : Equation37774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37775_implies_Equation2 (G : Type*) [Magma G] (h : Equation37775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37776_implies_Equation2 (G : Type*) [Magma G] (h : Equation37776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37778_implies_Equation2 (G : Type*) [Magma G] (h : Equation37778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = X1 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq15 eq14
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq10 eq20
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq63 eq31


@[equational_result]
theorem Equation37779_implies_Equation2 (G : Type*) [Magma G] (h : Equation37779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X0) ◇ (X4 ◇ X0)) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ X5) ◇ (X1 ◇ X6))) ◇ X0)) = X3 := superpose eq7 eq11
  have eq35 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ X2) = X4 := superpose eq7 eq9
  have eq57 (X0 X1 X3 X5 : G) : (X0 ◇ ((X1 ◇ X5) ◇ X0)) = X3 := superpose eq35 eq18
  have eq72 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq35 eq57
  have eq73 (X0 X3 : G) : X0 = X3 := superpose eq72 eq72
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq85 eq73


@[equational_result]
theorem Equation37780_implies_Equation2 (G : Type*) [Magma G] (h : Equation37780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X0) ◇ (X4 ◇ X0)) ◇ X5) ◇ X3) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X3) = X5 := superpose eq10 eq9
  have eq14 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq12 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq31 eq15


@[equational_result]
theorem Equation37781_implies_Equation2 (G : Type*) [Magma G] (h : Equation37781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X6 X7 : G) : (((((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X0) ◇ (X4 ◇ X0)) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X3)) ◇ X4) = X0 := superpose eq13 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq14 eq14
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation37783_implies_Equation2 (G : Type*) [Magma G] (h : Equation37783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37784_implies_Equation2 (G : Type*) [Magma G] (h : Equation37784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37785_implies_Equation2 (G : Type*) [Magma G] (h : Equation37785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37786_implies_Equation2 (G : Type*) [Magma G] (h : Equation37786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37788_implies_Equation2 (G : Type*) [Magma G] (h : Equation37788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37789_implies_Equation2 (G : Type*) [Magma G] (h : Equation37789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37790_implies_Equation2 (G : Type*) [Magma G] (h : Equation37790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37791_implies_Equation2 (G : Type*) [Magma G] (h : Equation37791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37793_implies_Equation2 (G : Type*) [Magma G] (h : Equation37793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37794_implies_Equation2 (G : Type*) [Magma G] (h : Equation37794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37795_implies_Equation2 (G : Type*) [Magma G] (h : Equation37795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37796_implies_Equation2 (G : Type*) [Magma G] (h : Equation37796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37798_implies_Equation2 (G : Type*) [Magma G] (h : Equation37798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37799_implies_Equation2 (G : Type*) [Magma G] (h : Equation37799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37800_implies_Equation2 (G : Type*) [Magma G] (h : Equation37800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37801_implies_Equation2 (G : Type*) [Magma G] (h : Equation37801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37802_implies_Equation2 (G : Type*) [Magma G] (h : Equation37802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37805_implies_Equation2 (G : Type*) [Magma G] (h : Equation37805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq35 eq21


@[equational_result]
theorem Equation37806_implies_Equation2 (G : Type*) [Magma G] (h : Equation37806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X0) ◇ X0)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq15 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37809_implies_Equation2 (G : Type*) [Magma G] (h : Equation37809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X2) ◇ X0)) ◇ X1) ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X0))) ◇ X2)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0))) ◇ X1)) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ (((X3 ◇ (X3 ◇ X4)) ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X1)) ◇ (((X3 ◇ (X3 ◇ X4)) ◇ ((X3 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X0))) ◇ X2))) ◇ X3) = X4 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ ((((X4 ◇ (X4 ◇ X5)) ◇ ((X4 ◇ (X4 ◇ X5)) ◇ X1)) ◇ (((X4 ◇ (X4 ◇ X5)) ◇ ((X4 ◇ (X4 ◇ X5)) ◇ X1)) ◇ X0)) ◇ ((((X4 ◇ (X4 ◇ X5)) ◇ ((X4 ◇ (X4 ◇ X5)) ◇ X1)) ◇ (((X4 ◇ (X4 ◇ X5)) ◇ ((X4 ◇ (X4 ◇ X5)) ◇ X1)) ◇ X0)) ◇ X2))) ◇ X3)))) ◇ X4) = X5 := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) = X0 := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ ((X5 ◇ (X5 ◇ X0)) ◇ ((X5 ◇ (X5 ◇ X0)) ◇ X3))) ◇ X4)) = (((X1 ◇ (((X2 ◇ ((X3 ◇ ((X4 ◇ ((X5 ◇ (X5 ◇ X0)) ◇ ((X5 ◇ (X5 ◇ X0)) ◇ X3))) ◇ X4)) ◇ X0)) ◇ X2) ◇ X5)) ◇ X1) ◇ ((X2 ◇ ((X3 ◇ ((X4 ◇ ((X5 ◇ (X5 ◇ X0)) ◇ ((X5 ◇ (X5 ◇ X0)) ◇ X3))) ◇ X4)) ◇ X0)) ◇ X2)) := superpose eq10 eq9
  have eq33 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ ((X3 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X0))) ◇ X3))) = X2 := superpose eq7 eq17
  have eq37 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq17 eq9
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq17 eq10
  have eq40 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X3) = (((X1 ◇ (((X2 ◇ (((X3 ◇ X0) ◇ X3) ◇ X0)) ◇ X2) ◇ ((X4 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4))) ◇ X1) ◇ ((X2 ◇ (((X3 ◇ X0) ◇ X3) ◇ X0)) ◇ X2)) := superpose eq17 eq9
  have eq42 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) = (((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X0)) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq17 eq7
  have eq268 (X0 X1 X2 : G) : ((((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) = X2 := superpose eq42 eq7
  have eq612 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq17 eq268
  have eq662 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq7 eq612
  have eq753 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X2))) = X0 := superpose eq662 eq33
  have eq793 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2))) = X0 := superpose eq662 eq753
  have eq1004 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2)) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2)) ◇ X2))) ◇ X3) := superpose eq14 eq7
  have eq1128 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (((X3 ◇ (((X4 ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X4) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X3) ◇ ((X4 ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X4)) := superpose eq17 eq22
  have eq1286 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq662 eq793
  have eq1308 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := superpose eq7 eq40
  have eq1452 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0) := superpose eq1286 eq10
  have eq1478 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X3 ◇ X0))) = X3 := superpose eq1004 eq13
  have eq1479 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2) = X0 := superpose eq1004 eq14
  have eq1516 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ X0))) ◇ X1) := superpose eq17 eq1479
  have eq1517 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) := superpose eq1452 eq1479
  have eq1525 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))) := superpose eq1479 eq1479
  have eq1613 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ X0)) ◇ X1) = ((X3 ◇ X0) ◇ X3) := superpose eq7 eq1516
  have eq1614 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X3 ◇ X0) ◇ X3) := superpose eq7 eq1613
  have eq1615 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := superpose eq1479 eq1517
  have eq1954 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2))))) ◇ X0) = X1 := superpose eq1614 eq1478
  have eq1975 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1)))) = X2 := superpose eq1478 eq1479
  have eq2022 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ X2) := superpose eq1975 eq7
  have eq2308 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq2022 eq1308
  have eq2323 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq1615 eq2308
  have eq2327 (X0 X1 X2 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq2323 eq37
  have eq2328 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X0) := superpose eq2323 eq38
  have eq2334 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (((X3 ◇ (((X4 ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X4) ◇ X0)) ◇ X3) ◇ ((X4 ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X4)) := superpose eq2323 eq1128
  have eq2693 (X0 X1 : G) : (((X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) ◇ X1) ◇ X0) = X0 := superpose eq2323 eq2327
  have eq2694 (X0 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose eq2323 eq2693
  have eq2695 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq2323 eq2694
  have eq2696 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq2323 eq2328
  have eq2697 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X0 := superpose eq2695 eq2696
  have eq2713 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (((X3 ◇ (((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0)) ◇ X3) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq2323 eq2334
  have eq2714 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (((X3 ◇ (((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X0) ◇ X0)) ◇ X3) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X0)) := superpose eq2695 eq2713
  have eq2715 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X3 ◇ (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0)) ◇ X3) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq2323 eq2714
  have eq2716 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (((X3 ◇ (X0 ◇ X0)) ◇ X3) ◇ X0) := superpose eq2697 eq2715
  have eq2717 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq2323 eq2716
  have eq2718 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq2323 eq2717
  have eq2722 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X0) = X1 := superpose eq2718 eq1954
  have eq2731 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq2323 eq2722
  have eq2732 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))) = X2 := superpose eq2731 eq1525
  have eq2735 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq2732 eq1479
  have eq2773 (X0 X2 : G) : X0 = X2 := superpose eq2735 eq2735
  have eq2781 (X0 : G) : sK0 ≠ X0 := superpose eq2773 eq8
  subsumption eq2781 eq2773


@[equational_result]
theorem Equation37810_implies_Equation2 (G : Type*) [Magma G] (h : Equation37810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation37813_implies_Equation2 (G : Type*) [Magma G] (h : Equation37813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq47 eq14


@[equational_result]
theorem Equation37814_implies_Equation2 (G : Type*) [Magma G] (h : Equation37814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37816_implies_Equation2 (G : Type*) [Magma G] (h : Equation37816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq61 eq20


@[equational_result]
theorem Equation37817_implies_Equation2 (G : Type*) [Magma G] (h : Equation37817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation37818_implies_Equation2 (G : Type*) [Magma G] (h : Equation37818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37819_implies_Equation2 (G : Type*) [Magma G] (h : Equation37819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation37823_implies_Equation2 (G : Type*) [Magma G] (h : Equation37823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ X0) ◇ X0)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq15 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq32 eq16


@[equational_result]
theorem Equation37825_implies_Equation2 (G : Type*) [Magma G] (h : Equation37825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37826_implies_Equation2 (G : Type*) [Magma G] (h : Equation37826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37827_implies_Equation2 (G : Type*) [Magma G] (h : Equation37827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37829_implies_Equation2 (G : Type*) [Magma G] (h : Equation37829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37830_implies_Equation2 (G : Type*) [Magma G] (h : Equation37830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37831_implies_Equation2 (G : Type*) [Magma G] (h : Equation37831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37833_implies_Equation2 (G : Type*) [Magma G] (h : Equation37833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37834_implies_Equation2 (G : Type*) [Magma G] (h : Equation37834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37835_implies_Equation2 (G : Type*) [Magma G] (h : Equation37835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37836_implies_Equation2 (G : Type*) [Magma G] (h : Equation37836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37839_implies_Equation2 (G : Type*) [Magma G] (h : Equation37839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ X2) = X0 := superpose eq9 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation37840_implies_Equation2 (G : Type*) [Magma G] (h : Equation37840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X0) ◇ X0)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq15 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq32 eq16


@[equational_result]
theorem Equation37842_implies_Equation2 (G : Type*) [Magma G] (h : Equation37842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37843_implies_Equation2 (G : Type*) [Magma G] (h : Equation37843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37844_implies_Equation2 (G : Type*) [Magma G] (h : Equation37844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37846_implies_Equation2 (G : Type*) [Magma G] (h : Equation37846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37847_implies_Equation2 (G : Type*) [Magma G] (h : Equation37847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation37848_implies_Equation2 (G : Type*) [Magma G] (h : Equation37848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37850_implies_Equation2 (G : Type*) [Magma G] (h : Equation37850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37851_implies_Equation2 (G : Type*) [Magma G] (h : Equation37851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37852_implies_Equation2 (G : Type*) [Magma G] (h : Equation37852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37853_implies_Equation2 (G : Type*) [Magma G] (h : Equation37853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37855_implies_Equation2 (G : Type*) [Magma G] (h : Equation37855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X5) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X4))) ◇ X0)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) = X2 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X4 : G) : ((X0 ◇ X4) ◇ (X1 ◇ (X1 ◇ X2))) = X4 := superpose eq11 eq7
  have eq27 (X0 X1 X2 X5 : G) : ((X0 ◇ X5) ◇ ((X1 ◇ X2) ◇ X0)) = X5 := superpose eq24 eq10
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0))) = X1 := superpose eq7 eq27
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq27
  have eq55 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X2 ◇ (X2 ◇ X3)))) = X1 := superpose eq35 eq29
  have eq59 (X0 X1 X5 : G) : (X0 ◇ X5) = X1 := superpose eq24 eq55
  have eq60 (X0 X5 : G) : X0 = X5 := superpose eq11 eq59
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq89 eq60


@[equational_result]
theorem Equation37856_implies_Equation2 (G : Type*) [Magma G] (h : Equation37856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X2) = X0 := superpose eq10 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation37857_implies_Equation2 (G : Type*) [Magma G] (h : Equation37857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X3) = X0 := superpose eq10 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation37858_implies_Equation2 (G : Type*) [Magma G] (h : Equation37858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X6 X7 : G) : (((X1 ◇ (((X2 ◇ (X3 ◇ (X3 ◇ X4))) ◇ X0) ◇ X0)) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq9
  have eq15 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq32 eq16


@[equational_result]
theorem Equation37860_implies_Equation2 (G : Type*) [Magma G] (h : Equation37860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37861_implies_Equation2 (G : Type*) [Magma G] (h : Equation37861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37862_implies_Equation2 (G : Type*) [Magma G] (h : Equation37862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37863_implies_Equation2 (G : Type*) [Magma G] (h : Equation37863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37865_implies_Equation2 (G : Type*) [Magma G] (h : Equation37865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37866_implies_Equation2 (G : Type*) [Magma G] (h : Equation37866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37867_implies_Equation2 (G : Type*) [Magma G] (h : Equation37867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37868_implies_Equation2 (G : Type*) [Magma G] (h : Equation37868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37870_implies_Equation2 (G : Type*) [Magma G] (h : Equation37870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37871_implies_Equation2 (G : Type*) [Magma G] (h : Equation37871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37872_implies_Equation2 (G : Type*) [Magma G] (h : Equation37872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37873_implies_Equation2 (G : Type*) [Magma G] (h : Equation37873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37875_implies_Equation2 (G : Type*) [Magma G] (h : Equation37875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37876_implies_Equation2 (G : Type*) [Magma G] (h : Equation37876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37877_implies_Equation2 (G : Type*) [Magma G] (h : Equation37877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37878_implies_Equation2 (G : Type*) [Magma G] (h : Equation37878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37879_implies_Equation2 (G : Type*) [Magma G] (h : Equation37879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37881_implies_Equation2 (G : Type*) [Magma G] (h : Equation37881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X1 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq16 eq15
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq10 eq22
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq65 eq33


@[equational_result]
theorem Equation37882_implies_Equation2 (G : Type*) [Magma G] (h : Equation37882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ X2) = X4 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq62 eq24


@[equational_result]
theorem Equation37883_implies_Equation2 (G : Type*) [Magma G] (h : Equation37883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37884_implies_Equation2 (G : Type*) [Magma G] (h : Equation37884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq15 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation37886_implies_Equation2 (G : Type*) [Magma G] (h : Equation37886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation37887_implies_Equation2 (G : Type*) [Magma G] (h : Equation37887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation37888_implies_Equation2 (G : Type*) [Magma G] (h : Equation37888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X1) ◇ X4) = X5 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq65 eq17


@[equational_result]
theorem Equation37889_implies_Equation2 (G : Type*) [Magma G] (h : Equation37889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation37891_implies_Equation2 (G : Type*) [Magma G] (h : Equation37891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq59 eq22


@[equational_result]
theorem Equation37892_implies_Equation2 (G : Type*) [Magma G] (h : Equation37892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X2) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq57 eq15


@[equational_result]
theorem Equation37893_implies_Equation2 (G : Type*) [Magma G] (h : Equation37893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37894_implies_Equation2 (G : Type*) [Magma G] (h : Equation37894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37896_implies_Equation2 (G : Type*) [Magma G] (h : Equation37896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq56 eq19


@[equational_result]
theorem Equation37897_implies_Equation2 (G : Type*) [Magma G] (h : Equation37897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37898_implies_Equation2 (G : Type*) [Magma G] (h : Equation37898 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation37899_implies_Equation2 (G : Type*) [Magma G] (h : Equation37899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37901_implies_Equation2 (G : Type*) [Magma G] (h : Equation37901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X7 : G) : (((X1 ◇ X0) ◇ X7) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation37902_implies_Equation2 (G : Type*) [Magma G] (h : Equation37902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37903_implies_Equation2 (G : Type*) [Magma G] (h : Equation37903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X5) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37904_implies_Equation2 (G : Type*) [Magma G] (h : Equation37904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X7) ◇ X7) = X6 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq34 eq16


@[equational_result]
theorem Equation37905_implies_Equation2 (G : Type*) [Magma G] (h : Equation37905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X8 : G) : (X0 ◇ X8) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation37907_implies_Equation2 (G : Type*) [Magma G] (h : Equation37907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X1 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq15 eq14
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq10 eq20
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq33 eq24


@[equational_result]
theorem Equation37908_implies_Equation2 (G : Type*) [Magma G] (h : Equation37908 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ X2) = X0 := superpose eq14 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq22 eq22
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq33 eq30


@[equational_result]
theorem Equation37909_implies_Equation2 (G : Type*) [Magma G] (h : Equation37909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ X3) = X0 := superpose eq12 eq7
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq21 eq21
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation37910_implies_Equation2 (G : Type*) [Magma G] (h : Equation37910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq15 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq32 eq16


@[equational_result]
theorem Equation37912_implies_Equation2 (G : Type*) [Magma G] (h : Equation37912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37913_implies_Equation2 (G : Type*) [Magma G] (h : Equation37913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37914_implies_Equation2 (G : Type*) [Magma G] (h : Equation37914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37915_implies_Equation2 (G : Type*) [Magma G] (h : Equation37915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37917_implies_Equation2 (G : Type*) [Magma G] (h : Equation37917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37918_implies_Equation2 (G : Type*) [Magma G] (h : Equation37918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37919_implies_Equation2 (G : Type*) [Magma G] (h : Equation37919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37920_implies_Equation2 (G : Type*) [Magma G] (h : Equation37920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37922_implies_Equation2 (G : Type*) [Magma G] (h : Equation37922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37923_implies_Equation2 (G : Type*) [Magma G] (h : Equation37923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37924_implies_Equation2 (G : Type*) [Magma G] (h : Equation37924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37925_implies_Equation2 (G : Type*) [Magma G] (h : Equation37925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37927_implies_Equation2 (G : Type*) [Magma G] (h : Equation37927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37928_implies_Equation2 (G : Type*) [Magma G] (h : Equation37928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37929_implies_Equation2 (G : Type*) [Magma G] (h : Equation37929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37930_implies_Equation2 (G : Type*) [Magma G] (h : Equation37930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37931_implies_Equation2 (G : Type*) [Magma G] (h : Equation37931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37933_implies_Equation2 (G : Type*) [Magma G] (h : Equation37933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X5) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X4 ◇ X3))) ◇ X0)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X1) = X5 := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) = X2 := superpose eq9 eq9
  have eq21 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ (X3 ◇ X0)) = X5 := superpose eq17 eq10
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq21
  have eq40 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq26 eq12
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq21 eq40
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq72 eq41


@[equational_result]
theorem Equation37934_implies_Equation2 (G : Type*) [Magma G] (h : Equation37934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X2) = X0 := superpose eq10 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation37935_implies_Equation2 (G : Type*) [Magma G] (h : Equation37935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X3) = X0 := superpose eq10 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation37936_implies_Equation2 (G : Type*) [Magma G] (h : Equation37936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq15 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq32 eq16


@[equational_result]
theorem Equation37938_implies_Equation2 (G : Type*) [Magma G] (h : Equation37938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37939_implies_Equation2 (G : Type*) [Magma G] (h : Equation37939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37940_implies_Equation2 (G : Type*) [Magma G] (h : Equation37940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37941_implies_Equation2 (G : Type*) [Magma G] (h : Equation37941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37943_implies_Equation2 (G : Type*) [Magma G] (h : Equation37943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37944_implies_Equation2 (G : Type*) [Magma G] (h : Equation37944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37945_implies_Equation2 (G : Type*) [Magma G] (h : Equation37945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37946_implies_Equation2 (G : Type*) [Magma G] (h : Equation37946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37948_implies_Equation2 (G : Type*) [Magma G] (h : Equation37948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37949_implies_Equation2 (G : Type*) [Magma G] (h : Equation37949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37950_implies_Equation2 (G : Type*) [Magma G] (h : Equation37950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37951_implies_Equation2 (G : Type*) [Magma G] (h : Equation37951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37953_implies_Equation2 (G : Type*) [Magma G] (h : Equation37953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37954_implies_Equation2 (G : Type*) [Magma G] (h : Equation37954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37955_implies_Equation2 (G : Type*) [Magma G] (h : Equation37955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37956_implies_Equation2 (G : Type*) [Magma G] (h : Equation37956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37957_implies_Equation2 (G : Type*) [Magma G] (h : Equation37957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37959_implies_Equation2 (G : Type*) [Magma G] (h : Equation37959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X1 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq15 eq14
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq9 eq20
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq62 eq30


@[equational_result]
theorem Equation37960_implies_Equation2 (G : Type*) [Magma G] (h : Equation37960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ X2) = X0 := superpose eq10 eq7
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq27 eq20


@[equational_result]
theorem Equation37961_implies_Equation2 (G : Type*) [Magma G] (h : Equation37961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq10 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq29 eq14


@[equational_result]
theorem Equation37962_implies_Equation2 (G : Type*) [Magma G] (h : Equation37962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq15 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq32 eq16


@[equational_result]
theorem Equation37964_implies_Equation2 (G : Type*) [Magma G] (h : Equation37964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37965_implies_Equation2 (G : Type*) [Magma G] (h : Equation37965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37966_implies_Equation2 (G : Type*) [Magma G] (h : Equation37966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37967_implies_Equation2 (G : Type*) [Magma G] (h : Equation37967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37969_implies_Equation2 (G : Type*) [Magma G] (h : Equation37969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37970_implies_Equation2 (G : Type*) [Magma G] (h : Equation37970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37971_implies_Equation2 (G : Type*) [Magma G] (h : Equation37971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37972_implies_Equation2 (G : Type*) [Magma G] (h : Equation37972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37974_implies_Equation2 (G : Type*) [Magma G] (h : Equation37974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37975_implies_Equation2 (G : Type*) [Magma G] (h : Equation37975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37976_implies_Equation2 (G : Type*) [Magma G] (h : Equation37976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation37977_implies_Equation2 (G : Type*) [Magma G] (h : Equation37977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37979_implies_Equation2 (G : Type*) [Magma G] (h : Equation37979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37980_implies_Equation2 (G : Type*) [Magma G] (h : Equation37980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37981_implies_Equation2 (G : Type*) [Magma G] (h : Equation37981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37982_implies_Equation2 (G : Type*) [Magma G] (h : Equation37982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37983_implies_Equation2 (G : Type*) [Magma G] (h : Equation37983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37985_implies_Equation2 (G : Type*) [Magma G] (h : Equation37985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X7 : G) : (((X1 ◇ X0) ◇ X7) ◇ X1) = X7 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X1 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq16 eq15
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq10 eq22
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq65 eq33


@[equational_result]
theorem Equation37986_implies_Equation2 (G : Type*) [Magma G] (h : Equation37986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X7 : G) : ((X0 ◇ X7) ◇ X2) = X7 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ X2) = X0 := superpose eq11 eq7
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq13 eq13
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq30 eq23


@[equational_result]
theorem Equation37987_implies_Equation2 (G : Type*) [Magma G] (h : Equation37987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X7 : G) : (((X1 ◇ X0) ◇ X7) ◇ X4) = X7 := superpose eq7 eq7
  have eq11 (X0 X4 X7 : G) : ((X0 ◇ X7) ◇ X4) = X7 := superpose eq7 eq7
  have eq15 (X0 X4 X7 : G) : (X0 ◇ X4) = X7 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq32 eq16


@[equational_result]
theorem Equation37988_implies_Equation2 (G : Type*) [Magma G] (h : Equation37988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X7) ◇ X6) = X7 := superpose eq7 eq7
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = X7 := superpose eq7 eq7
  have eq15 (X0 X6 X7 : G) : (X0 ◇ X6) = X7 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq32 eq16


@[equational_result]
theorem Equation37989_implies_Equation2 (G : Type*) [Magma G] (h : Equation37989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X8 X9 : G) : (((X1 ◇ X0) ◇ X8) ◇ X9) = X8 := superpose eq7 eq7
  have eq11 (X0 X8 X9 : G) : ((X0 ◇ X8) ◇ X9) = X8 := superpose eq7 eq7
  have eq15 (X0 X8 X9 : G) : (X0 ◇ X9) = X8 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq32 eq16


@[equational_result]
theorem Equation37991_implies_Equation2 (G : Type*) [Magma G] (h : Equation37991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37992_implies_Equation2 (G : Type*) [Magma G] (h : Equation37992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37993_implies_Equation2 (G : Type*) [Magma G] (h : Equation37993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37994_implies_Equation2 (G : Type*) [Magma G] (h : Equation37994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37995_implies_Equation2 (G : Type*) [Magma G] (h : Equation37995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X1) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37997_implies_Equation2 (G : Type*) [Magma G] (h : Equation37997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation37998_implies_Equation2 (G : Type*) [Magma G] (h : Equation37998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation37999_implies_Equation2 (G : Type*) [Magma G] (h : Equation37999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38000_implies_Equation2 (G : Type*) [Magma G] (h : Equation38000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38001_implies_Equation2 (G : Type*) [Magma G] (h : Equation38001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38003_implies_Equation2 (G : Type*) [Magma G] (h : Equation38003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38004_implies_Equation2 (G : Type*) [Magma G] (h : Equation38004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38005_implies_Equation2 (G : Type*) [Magma G] (h : Equation38005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38006_implies_Equation2 (G : Type*) [Magma G] (h : Equation38006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38007_implies_Equation2 (G : Type*) [Magma G] (h : Equation38007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X3) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38009_implies_Equation2 (G : Type*) [Magma G] (h : Equation38009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38010_implies_Equation2 (G : Type*) [Magma G] (h : Equation38010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38011_implies_Equation2 (G : Type*) [Magma G] (h : Equation38011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38012_implies_Equation2 (G : Type*) [Magma G] (h : Equation38012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38013_implies_Equation2 (G : Type*) [Magma G] (h : Equation38013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38015_implies_Equation2 (G : Type*) [Magma G] (h : Equation38015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38016_implies_Equation2 (G : Type*) [Magma G] (h : Equation38016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38017_implies_Equation2 (G : Type*) [Magma G] (h : Equation38017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38018_implies_Equation2 (G : Type*) [Magma G] (h : Equation38018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38019_implies_Equation2 (G : Type*) [Magma G] (h : Equation38019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38020_implies_Equation2 (G : Type*) [Magma G] (h : Equation38020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38226_implies_Equation2 (G : Type*) [Magma G] (h : Equation38226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation38229_implies_Equation2 (G : Type*) [Magma G] (h : Equation38229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation38231_implies_Equation2 (G : Type*) [Magma G] (h : Equation38231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation38232_implies_Equation2 (G : Type*) [Magma G] (h : Equation38232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation38233_implies_Equation2 (G : Type*) [Magma G] (h : Equation38233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38236_implies_Equation2 (G : Type*) [Magma G] (h : Equation38236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq10 eq7
  have eq13 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq10 eq12
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq20 eq15


@[equational_result]
theorem Equation38239_implies_Equation2 (G : Type*) [Magma G] (h : Equation38239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq66 eq22


@[equational_result]
theorem Equation38241_implies_Equation2 (G : Type*) [Magma G] (h : Equation38241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq54 eq16


@[equational_result]
theorem Equation38243_implies_Equation2 (G : Type*) [Magma G] (h : Equation38243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38245_implies_Equation2 (G : Type*) [Magma G] (h : Equation38245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X3) ◇ ((((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0)) ◇ X4)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0))) = X1 := superpose eq7 eq9
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq17 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) = X0 := superpose eq7 eq9
  have eq18 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq9 eq7
  have eq21 (X0 X3 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X3))) = X0 := superpose eq9 eq10
  have eq31 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq18 eq18
  have eq32 (X0 X1 X2 : G) : (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X2))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq10 eq18
  have eq43 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq21
  have eq55 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq31 eq43
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq55 eq32
  have eq58 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) = X0 := superpose eq55 eq10
  have eq59 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X3) ◇ (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) ◇ X4)) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0))) = X1 := superpose eq55 eq11
  have eq63 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq55 eq17
  have eq69 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq55 eq15
  have eq80 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq55 eq56
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq55 eq58
  have eq84 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X3) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X1 := superpose eq55 eq59
  have eq85 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X3) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X1 := superpose eq55 eq84
  have eq91 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq55 eq63
  have eq92 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq55 eq91
  have eq93 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq92 eq80
  have eq94 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq92 eq93
  have eq95 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq94 eq83
  have eq101 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq95 eq69
  have eq102 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X3) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X1 := superpose eq101 eq85
  have eq115 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X3) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X1 := superpose eq101 eq102
  have eq116 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X1 := superpose eq101 eq115
  have eq117 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq101 eq116
  have eq161 (X0 X1 : G) : X0 = X1 := superpose eq101 eq117
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq161 eq8
  subsumption eq163 eq161


@[equational_result]
theorem Equation38246_implies_Equation2 (G : Type*) [Magma G] (h : Equation38246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq9 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq9 eq11
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq19 eq14


@[equational_result]
theorem Equation38247_implies_Equation2 (G : Type*) [Magma G] (h : Equation38247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq10 eq13
  have eq15 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq14 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation38251_implies_Equation2 (G : Type*) [Magma G] (h : Equation38251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation38254_implies_Equation2 (G : Type*) [Magma G] (h : Equation38254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation38255_implies_Equation2 (G : Type*) [Magma G] (h : Equation38255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation38257_implies_Equation2 (G : Type*) [Magma G] (h : Equation38257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq70 eq19


@[equational_result]
theorem Equation38258_implies_Equation2 (G : Type*) [Magma G] (h : Equation38258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation38259_implies_Equation2 (G : Type*) [Magma G] (h : Equation38259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation38260_implies_Equation2 (G : Type*) [Magma G] (h : Equation38260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38263_implies_Equation2 (G : Type*) [Magma G] (h : Equation38263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq23 eq16


@[equational_result]
theorem Equation38266_implies_Equation2 (G : Type*) [Magma G] (h : Equation38266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ X2) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) = (((X1 ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0)) := superpose eq10 eq10
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) := superpose eq10 eq10
  have eq28 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) = X0 := superpose eq10 eq7
  have eq34 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) := superpose eq10 eq14
  have eq35 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) := superpose eq10 eq34
  have eq40 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) := superpose eq24 eq35
  have eq45 (X0 X1 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X3) = X0 := superpose eq10 eq28
  have eq46 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) = X0 := superpose eq24 eq45
  have eq47 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq46 eq40
  have eq48 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq47 eq46
  have eq61 (X0 X3 : G) : X0 = X3 := superpose eq48 eq48
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq63 eq61


@[equational_result]
theorem Equation38268_implies_Equation2 (G : Type*) [Magma G] (h : Equation38268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation38270_implies_Equation2 (G : Type*) [Magma G] (h : Equation38270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38273_implies_Equation2 (G : Type*) [Magma G] (h : Equation38273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38276_implies_Equation2 (G : Type*) [Magma G] (h : Equation38276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq80 eq57


@[equational_result]
theorem Equation38278_implies_Equation2 (G : Type*) [Magma G] (h : Equation38278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation38279_implies_Equation2 (G : Type*) [Magma G] (h : Equation38279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = (((X1 ◇ X0) ◇ X3) ◇ X3) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq7 eq10
  have eq24 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X1) ◇ X1)) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 X2 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X4) ◇ X4) = X1 := superpose eq10 eq7
  have eq52 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X5) ◇ X5) = ((X3 ◇ (((X1 ◇ X4) ◇ X3) ◇ X3)) ◇ X4) := superpose eq10 eq9
  have eq56 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X0) = ((X3 ◇ (((X1 ◇ X4) ◇ X3) ◇ X3)) ◇ X4) := superpose eq9 eq9
  have eq81 (X1 X3 X4 : G) : ((X3 ◇ (((X1 ◇ X4) ◇ X3) ◇ X3)) ◇ X4) = X1 := superpose eq26 eq52
  have eq82 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X0) = X1 := superpose eq81 eq56
  have eq86 (X0 X2 X3 : G) : (X3 ◇ ((X2 ◇ X3) ◇ X3)) = X0 := superpose eq7 eq21
  have eq116 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X4) ◇ X4) = ((X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0)) ◇ X3) := superpose eq21 eq9
  have eq144 (X1 X3 X4 : G) : (X1 ◇ X3) = (((X3 ◇ (X1 ◇ X3)) ◇ X4) ◇ X4) := superpose eq24 eq116
  have eq150 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq144 eq82
  have eq191 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq150 eq86
  have eq273 (X0 X3 : G) : X0 = X3 := superpose eq191 eq191
  have eq275 (X0 : G) : sK0 ≠ X0 := superpose eq273 eq8
  subsumption eq275 eq273


@[equational_result]
theorem Equation38280_implies_Equation2 (G : Type*) [Magma G] (h : Equation38280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38282_implies_Equation2 (G : Type*) [Magma G] (h : Equation38282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = (((X1 ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ (X1 ◇ (X0 ◇ X3))) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (X1 ◇ X1)) := superpose eq10 eq10
  have eq16 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = (((X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ X1) := superpose eq10 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) ◇ X4)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = (((X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X3 ◇ ((((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) ◇ X4)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) ◇ X3) := superpose eq10 eq9
  have eq23 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) ◇ ((X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ X4)) ◇ X1) = (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ (((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) ◇ ((X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ X4)) ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) := superpose eq10 eq9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) = (((X1 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) ◇ X1) := superpose eq7 eq9
  have eq37 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := superpose eq16 eq7
  have eq61 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0))) := superpose eq9 eq37
  have eq203 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) = (((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))))) ◇ X0) := superpose eq14 eq17
  have eq265 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X0)) = (((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X0))) ◇ X1) := superpose eq7 eq24
  have eq516 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq265 eq7
  have eq622 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0)) := superpose eq516 eq7
  have eq637 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0)) := superpose eq7 eq622
  have eq638 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq637 eq61
  have eq706 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq637 eq265
  have eq708 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq637 eq9
  have eq712 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq637 eq16
  have eq713 (X0 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq637 eq7
  have eq788 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq708 eq637
  have eq789 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq708 eq638
  have eq868 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq706 eq7
  have eq869 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq706 eq9
  have eq897 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq712 eq868
  have eq975 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq897 eq788
  have eq986 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq712 eq869
  have eq1130 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ X0) := superpose eq975 eq9
  have eq1131 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq975 eq10
  have eq1132 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq975 eq11
  have eq1182 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq897 eq1130
  have eq1183 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq897 eq1131
  have eq1184 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq897 eq1132
  have eq1676 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq975 eq708
  have eq1696 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq897 eq1676
  have eq1699 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq1696 eq708
  have eq1714 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq1696 eq789
  have eq2584 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq1182 eq986
  have eq2589 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq2584 eq1714
  have eq2590 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq897 eq2589
  have eq2619 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq2590 eq713
  have eq2752 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq1183 eq2619
  have eq2865 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = (((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ X0) := superpose eq2752 eq203
  have eq2975 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq2752 eq2865
  have eq2976 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq2590 eq2975
  have eq2977 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq2752 eq2976
  have eq2978 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq2977 eq1184
  have eq3084 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X3))) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) := superpose eq2977 eq11
  have eq3797 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ X4)) ◇ X1) = (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ X4)) ◇ X1)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) := superpose eq2977 eq23
  have eq3835 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) ◇ X4)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = (((X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X3 ◇ (((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X3) ◇ X4)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) ◇ X3) := superpose eq2977 eq20
  have eq3868 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq2977 eq1699
  have eq3918 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq2977 eq2978
  have eq3919 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq2977 eq3918
  have eq4818 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq2977 eq3868
  have eq4821 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq4818 eq3919
  have eq4855 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq4821 eq7
  have eq4890 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq2977 eq4855
  have eq5052 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))) = (((((((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))))) ◇ X6)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))))) ◇ (((((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))))) ◇ X6)) ◇ X0)) := superpose eq3835 eq3084
  have eq5172 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq4890 eq7
  have eq5265 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq2977 eq5172
  have eq5266 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq4821 eq5265
  have eq5267 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq2977 eq5266
  have eq5279 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ X4)) = (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3))) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) ◇ X4))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)))) := superpose eq5267 eq3797
  have eq5297 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))) = ((((((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))))) ◇ X6)) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))))) ◇ ((((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))))) ◇ X6))) := superpose eq5267 eq5052
  have eq5495 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X4)) = (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X4))) ◇ (X1 ◇ X2)) := superpose eq5267 eq5279
  have eq5496 (X0 X1 X3 X4 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X4)) = (((X0 ◇ ((X1 ◇ X0) ◇ X3)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X4))) ◇ X1) := superpose eq5267 eq5495
  have eq5497 (X0 X1 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X1) = (X1 ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq5267 eq5496
  have eq5498 (X0 X1 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X1) = X1 := superpose eq5267 eq5497
  have eq5499 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq5267 eq5498
  have eq5545 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))) = (((((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))))) ◇ (((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))))) := superpose eq5267 eq5297
  have eq5546 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))) = ((((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))))) ◇ ((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))) := superpose eq5267 eq5545
  have eq5547 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) = (((X0 ◇ X1) ◇ (((X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X0 ◇ X1)) ◇ X5)) ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))) := superpose eq5499 eq5546
  have eq5548 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) = (((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X5)) ◇ X2) := superpose eq5267 eq5547
  have eq5549 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) = X2 := superpose eq5499 eq5548
  have eq5550 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X3) = X2 := superpose eq5267 eq5549
  have eq5551 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq5267 eq5550
  have eq5552 (X0 X1 : G) : X0 = X1 := superpose eq2977 eq5551
  have eq5560 (X0 : G) : sK0 ≠ X0 := superpose eq5552 eq8
  subsumption eq5560 eq5552


@[equational_result]
theorem Equation38284_implies_Equation2 (G : Type*) [Magma G] (h : Equation38284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38286_implies_Equation2 (G : Type*) [Magma G] (h : Equation38286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = (((X1 ◇ (X0 ◇ X3)) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (((X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ X1) ◇ X1) := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = (((X1 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X4)) ◇ X1) ◇ X1) := superpose eq7 eq9
  have eq30 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) ◇ X0) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ X0) ◇ X0) := superpose eq10 eq9
  have eq34 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) ◇ X0) = (((X0 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq45 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) ◇ X4)) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) = ((X0 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) := superpose eq7 eq9
  have eq54 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := superpose eq9 eq7
  have eq64 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X4)) = (((X0 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X0)) ◇ X0) ◇ X0) := superpose eq9 eq10
  have eq66 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) ◇ X0) := superpose eq7 eq30
  have eq67 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ X1) := superpose eq66 eq11
  have eq70 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = (((X0 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X0) ◇ X0) := superpose eq66 eq34
  have eq73 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) = (((((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) ◇ X1) ◇ X4)) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) := superpose eq67 eq45
  have eq74 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) = (((((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2)) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ X4)) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) := superpose eq67 eq73
  have eq85 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X4)) := superpose eq70 eq64
  have eq87 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq85 eq28
  have eq95 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq67 eq67
  have eq117 (X0 X1 X2 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) ◇ X1) ◇ X1) = X0 := superpose eq67 eq7
  have eq137 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2)) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ X4)) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) := superpose eq95 eq74
  have eq141 (X0 X1 X2 : G) : ((((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X1) ◇ X1) = X0 := superpose eq87 eq117
  have eq142 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq141
  have eq143 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) = (((((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4)) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (X1 ◇ X2))) := superpose eq142 eq137
  have eq146 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ ((X1 ◇ X0) ◇ X3)) = X0 := superpose eq142 eq54
  have eq204 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) = ((((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4)) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq142 eq143
  have eq205 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4)) ◇ (X1 ◇ X2)) := superpose eq142 eq204
  have eq206 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X4)) ◇ X1) := superpose eq142 eq205
  have eq207 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq142 eq206
  have eq208 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq142 eq207
  have eq209 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq142 eq208
  have eq210 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq142 eq209
  have eq213 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := superpose eq142 eq146
  have eq214 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X1) ◇ X1) = X0 := superpose eq142 eq213
  have eq215 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X1) = X0 := superpose eq142 eq214
  have eq216 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq142 eq215
  have eq303 (X0 X1 : G) : X0 = X1 := superpose eq210 eq216
  have eq308 (X0 : G) : sK0 ≠ X0 := superpose eq303 eq8
  subsumption eq308 eq303


@[equational_result]
theorem Equation38287_implies_Equation2 (G : Type*) [Magma G] (h : Equation38287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) = (((X1 ◇ (X0 ◇ X3)) ◇ X1) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ X2) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) = X0 := superpose eq7 eq10
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X2)) ◇ X1) = X0 := superpose eq7 eq9
  have eq90 (X0 X1 X2 X3 : G) : (((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) ◇ X3) = X1 := superpose eq14 eq7
  have eq104 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = ((X3 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X2)) ◇ X3) := superpose eq9 eq40
  have eq126 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X3)) = ((X3 ◇ X1) ◇ X3) := superpose eq7 eq104
  have eq134 (X0 X1 X2 X3 : G) : (((X2 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X2) ◇ X3) = X1 := superpose eq126 eq90
  have eq146 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq40 eq134
  have eq147 (X0 X3 : G) : X0 = X3 := superpose eq7 eq146
  have eq250 (X0 : G) : sK0 ≠ X0 := superpose eq147 eq8
  subsumption eq250 eq147


@[equational_result]
theorem Equation38288_implies_Equation2 (G : Type*) [Magma G] (h : Equation38288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq60 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq83 eq60


@[equational_result]
theorem Equation38292_implies_Equation2 (G : Type*) [Magma G] (h : Equation38292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation38294_implies_Equation2 (G : Type*) [Magma G] (h : Equation38294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = X3 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq71 eq20


@[equational_result]
theorem Equation38295_implies_Equation2 (G : Type*) [Magma G] (h : Equation38295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation38296_implies_Equation2 (G : Type*) [Magma G] (h : Equation38296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X4)) = X3 := superpose eq7 eq7
  have eq51 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq7 eq51
  have eq194 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq194 eq64


@[equational_result]
theorem Equation38297_implies_Equation2 (G : Type*) [Magma G] (h : Equation38297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38299_implies_Equation2 (G : Type*) [Magma G] (h : Equation38299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ X3) ◇ X0)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)))) = X0 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)) ◇ X1) := superpose eq10 eq7
  have eq33 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) = X0 := superpose eq7 eq20
  have eq77 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq33
  have eq82 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq33
  have eq91 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X1 := superpose eq33 eq33
  have eq109 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq77 eq18
  have eq128 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq109 eq10
  have eq142 (X0 X1 X2 : G) : (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq77 eq128
  have eq143 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq142 eq82
  have eq147 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq143 eq142
  have eq159 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X1 := superpose eq7 eq77
  have eq161 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq33 eq77
  have eq197 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq161 eq91
  have eq221 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq197 eq147
  have eq222 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq197 eq159
  have eq225 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq222 eq161
  have eq227 (X0 X2 : G) : X0 = X2 := superpose eq221 eq225
  have eq244 (X0 : G) : sK0 ≠ X0 := superpose eq227 eq8
  subsumption eq244 eq227


@[equational_result]
theorem Equation38300_implies_Equation2 (G : Type*) [Magma G] (h : Equation38300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation38301_implies_Equation2 (G : Type*) [Magma G] (h : Equation38301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation38304_implies_Equation2 (G : Type*) [Magma G] (h : Equation38304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq10 eq10
  have eq50 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq142 eq50


@[equational_result]
theorem Equation38305_implies_Equation2 (G : Type*) [Magma G] (h : Equation38305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation38308_implies_Equation2 (G : Type*) [Magma G] (h : Equation38308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation38309_implies_Equation2 (G : Type*) [Magma G] (h : Equation38309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38311_implies_Equation2 (G : Type*) [Magma G] (h : Equation38311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation38312_implies_Equation2 (G : Type*) [Magma G] (h : Equation38312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation38313_implies_Equation2 (G : Type*) [Magma G] (h : Equation38313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq30 eq18


@[equational_result]
theorem Equation38314_implies_Equation2 (G : Type*) [Magma G] (h : Equation38314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38318_implies_Equation2 (G : Type*) [Magma G] (h : Equation38318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38320_implies_Equation2 (G : Type*) [Magma G] (h : Equation38320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3)) ◇ X3) ◇ X3) := superpose eq10 eq7
  have eq26 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq7 eq24
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq26 eq7
  have eq45 (X0 X2 : G) : X0 = X2 := superpose eq29 eq29
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq47 eq45


@[equational_result]
theorem Equation38321_implies_Equation2 (G : Type*) [Magma G] (h : Equation38321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ X2) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X3 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X2)) ◇ X3) ◇ X1) := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1)) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X1 := superpose eq10 eq7
  have eq81 (X0 X1 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) = X0 := superpose eq10 eq20
  have eq82 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0))) = X1 := superpose eq10 eq20
  have eq91 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X2) ◇ X2) ◇ ((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X2)) ◇ X1) := superpose eq20 eq10
  have eq95 (X0 X1 X2 X3 : G) : (((((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) ◇ (X1 ◇ X2)) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) ◇ (X1 ◇ X2))) ◇ X2) = X1 := superpose eq20 eq7
  have eq115 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq21 eq20
  have eq127 (X0 X1 X2 X3 : G) : ((((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) ◇ (X1 ◇ X2)))) ◇ X2) = X1 := superpose eq115 eq95
  have eq128 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X2) ◇ (X2 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X2))) ◇ X1) := superpose eq115 eq91
  have eq132 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X1)) ◇ X2) = X0 := superpose eq115 eq7
  have eq133 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = (((X3 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X2) ◇ X2))) ◇ X3) ◇ X1) := superpose eq115 eq11
  have eq197 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ X2) ◇ X0) ◇ X1) := superpose eq20 eq128
  have eq201 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ ((X2 ◇ (((X0 ◇ X3) ◇ X2) ◇ X2)) ◇ X3)) ◇ X1) := superpose eq115 eq133
  have eq202 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = ((X3 ◇ X0) ◇ X1) := superpose eq132 eq201
  have eq203 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq202 eq197
  have eq209 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))))) ◇ X2) = X1 := superpose eq202 eq127
  have eq211 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq202 eq82
  have eq212 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq203 eq81
  have eq213 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq212 eq211
  have eq217 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq213 eq209
  have eq239 (X0 X3 : G) : X0 = X3 := superpose eq217 eq217
  have eq250 (X0 : G) : sK0 ≠ X0 := superpose eq239 eq8
  subsumption eq250 eq239


@[equational_result]
theorem Equation38322_implies_Equation2 (G : Type*) [Magma G] (h : Equation38322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq60 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq84 eq60


@[equational_result]
theorem Equation38324_implies_Equation2 (G : Type*) [Magma G] (h : Equation38324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X3) = (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (((X1 ◇ X0) ◇ X2) ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X2) ◇ X1)) = X0 := superpose eq7 eq10
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X2) = X0 := superpose eq7 eq9
  have eq66 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (X3 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X0) ◇ X3)) := superpose eq10 eq15
  have eq85 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (X3 ◇ ((X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0)) ◇ X3)) := superpose eq10 eq66
  have eq86 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (X3 ◇ (X1 ◇ X2)) := superpose eq37 eq85
  have eq133 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq86
  have eq265 (X0 X4 : G) : X0 = X4 := superpose eq7 eq133
  have eq417 (X0 : G) : sK0 ≠ X0 := superpose eq265 eq8
  subsumption eq417 eq265


@[equational_result]
theorem Equation38326_implies_Equation2 (G : Type*) [Magma G] (h : Equation38326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation38328_implies_Equation2 (G : Type*) [Magma G] (h : Equation38328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq67 eq19


@[equational_result]
theorem Equation38329_implies_Equation2 (G : Type*) [Magma G] (h : Equation38329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation38330_implies_Equation2 (G : Type*) [Magma G] (h : Equation38330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X2)) = (((X1 ◇ X0) ◇ X4) ◇ X4) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1)))) = X3 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X3) ◇ X4) ◇ X1)) = X0 := superpose eq7 eq10
  have eq42 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ ((X4 ◇ X5) ◇ (X6 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X6)))) = X4 := superpose eq10 eq11
  have eq60 (X0 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq25 eq42
  have eq69 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq60 eq22
  have eq86 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq69 eq60
  have eq96 (X0 X3 : G) : X0 = X3 := superpose eq86 eq86
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq101 eq96


@[equational_result]
theorem Equation38331_implies_Equation2 (G : Type*) [Magma G] (h : Equation38331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38333_implies_Equation2 (G : Type*) [Magma G] (h : Equation38333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X2)) = (((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2))) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X1 ◇ X3) ◇ X3) ◇ ((((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ X4) ◇ X4)) ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0))) = X1 := superpose eq7 eq11
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ ((((X2 ◇ X3) ◇ X3) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = X2 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X0) = (((X1 ◇ (X0 ◇ ((((X0 ◇ X3) ◇ X3) ◇ ((X2 ◇ X4) ◇ X4)) ◇ X2))) ◇ (X2 ◇ X0)) ◇ X1) := superpose eq11 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = ((X0 ◇ X1) ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X3) ◇ X3))) := superpose eq7 eq12
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X2) ◇ X2))) := superpose eq7 eq12
  have eq27 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ ((((X0 ◇ X2) ◇ X2) ◇ (((X1 ◇ X0) ◇ X3) ◇ X3)) ◇ (X1 ◇ X0))))) = X1 := superpose eq11 eq12
  have eq31 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = (((X1 ◇ (X0 ◇ (X0 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3)))) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) := superpose eq12 eq7
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = (((X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) ◇ X2) := superpose eq7 eq10
  have eq202 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X2)) ◇ (((((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3)) ◇ X4) ◇ X4) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq25 eq20
  have eq336 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((((X0 ◇ X2) ◇ X2) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X3) ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))))) := superpose eq7 eq27
  have eq405 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq13 eq336
  have eq428 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0))) ◇ X0) ◇ X2) = X0 := superpose eq405 eq7
  have eq440 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := superpose eq405 eq20
  have eq690 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0) = ((X0 ◇ X1) ◇ (((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X4) ◇ X4))))) := superpose eq25 eq22
  have eq1100 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0) = (((X2 ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ X0)) ◇ X2) := superpose eq13 eq21
  have eq1136 (X0 X2 : G) : (((X2 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq7 eq1100
  have eq1155 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := superpose eq7 eq1136
  have eq1156 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)))) = X0 := superpose eq428 eq1136
  have eq1159 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq10 eq1136
  have eq1161 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq40 eq1136
  have eq1262 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3)))) = X0 := superpose eq1159 eq440
  have eq1275 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) = X0 := superpose eq1159 eq1156
  have eq1279 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1155 eq1275
  have eq1281 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X0 := superpose eq1262 eq1161
  have eq1298 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ X0) := superpose eq1281 eq405
  have eq1370 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq1279 eq1298
  have eq1402 (X0 X1 X3 X4 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3)) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3)) ◇ X4) ◇ X4) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq1370 eq202
  have eq1414 (X0 X1 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0) = ((X0 ◇ X1) ◇ (((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X4) ◇ X4))))) := superpose eq1370 eq690
  have eq1630 (X0 X3 X4 : G) : (X0 ◇ ((X0 ◇ X3) ◇ X3)) = (X0 ◇ (((((X0 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X4) ◇ X4) ◇ X0) ◇ X0)) := superpose eq1370 eq1402
  have eq1631 (X0 X4 : G) : (X0 ◇ ((((X0 ◇ X4) ◇ X4) ◇ X0) ◇ X0)) = X0 := superpose eq1370 eq1630
  have eq1632 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X0 := superpose eq1136 eq1631
  have eq1716 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0) = ((X0 ◇ X1) ◇ (((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq1370 eq1414
  have eq1717 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0) = ((X0 ◇ X1) ◇ (((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq1279 eq1716
  have eq1718 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0) := superpose eq1632 eq1717
  have eq1919 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq1718 eq7
  have eq2183 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = (((X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2)))) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) := superpose eq1919 eq31
  have eq2448 (X0 X1 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X1) = X0 := superpose eq1919 eq2183
  have eq2449 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq1632 eq2448
  have eq2450 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq1919 eq2449
  have eq2640 (X0 X2 : G) : X0 = X2 := superpose eq2450 eq2450
  have eq2642 (X0 : G) : sK0 ≠ X0 := superpose eq2640 eq8
  subsumption eq2642 eq2640


@[equational_result]
theorem Equation38334_implies_Equation2 (G : Type*) [Magma G] (h : Equation38334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq11 eq14
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation38335_implies_Equation2 (G : Type*) [Magma G] (h : Equation38335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38337_implies_Equation2 (G : Type*) [Magma G] (h : Equation38337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X3)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq18 (X0 X1 X4 : G) : (((X4 ◇ X1) ◇ X4) ◇ X4) = X0 := superpose eq7 eq10
  have eq102 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq201 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq201 eq102


@[equational_result]
theorem Equation38339_implies_Equation2 (G : Type*) [Magma G] (h : Equation38339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation38342_implies_Equation2 (G : Type*) [Magma G] (h : Equation38342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation38343_implies_Equation2 (G : Type*) [Magma G] (h : Equation38343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38345_implies_Equation2 (G : Type*) [Magma G] (h : Equation38345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq76 eq21


@[equational_result]
theorem Equation38346_implies_Equation2 (G : Type*) [Magma G] (h : Equation38346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38347_implies_Equation2 (G : Type*) [Magma G] (h : Equation38347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq30 eq18


@[equational_result]
theorem Equation38348_implies_Equation2 (G : Type*) [Magma G] (h : Equation38348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38350_implies_Equation2 (G : Type*) [Magma G] (h : Equation38350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ ((((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X4) ◇ X5)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X4))) = X0 := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq11 eq7
  have eq31 (X0 X1 X2 X5 X6 X7 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X5) ◇ (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X5) ◇ X6) ◇ X7))) := superpose eq12 eq12
  have eq32 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ ((X0 ◇ X4) ◇ X5))) := superpose eq7 eq12
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq26 eq26
  have eq80 (X0 X1 X2 X5 X6 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X5) ◇ ((X0 ◇ X5) ◇ X6)) := superpose eq57 eq31
  have eq86 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = (X0 ◇ (X0 ◇ X4)) := superpose eq57 eq32
  have eq106 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq57 eq86
  have eq107 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq106 eq80
  have eq111 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq107 eq26
  have eq122 (X0 X2 : G) : X0 = X2 := superpose eq111 eq111
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq8
  subsumption eq124 eq122


@[equational_result]
theorem Equation38351_implies_Equation2 (G : Type*) [Magma G] (h : Equation38351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq11 eq14
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation38352_implies_Equation2 (G : Type*) [Magma G] (h : Equation38352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38353_implies_Equation2 (G : Type*) [Magma G] (h : Equation38353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X7 : G) : ((X0 ◇ X4) ◇ X7) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38355_implies_Equation2 (G : Type*) [Magma G] (h : Equation38355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X4)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq18 (X0 X1 X6 : G) : (((X6 ◇ X1) ◇ X6) ◇ X6) = X0 := superpose eq7 eq10
  have eq106 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq208 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq208 eq106


@[equational_result]
theorem Equation38356_implies_Equation2 (G : Type*) [Magma G] (h : Equation38356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X2) = (((X1 ◇ (X0 ◇ X5)) ◇ X1) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X4)) = (((X1 ◇ X0) ◇ X1) ◇ X2) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X3) = X1 := superpose eq10 eq7
  have eq31 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X3))) ◇ X4) ◇ X3) = X2 := superpose eq10 eq7
  have eq69 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (((X1 ◇ X4) ◇ X5) ◇ X6)) ◇ X3) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X5) := superpose eq10 eq9
  have eq102 (X1 X3 X4 X5 X6 : G) : ((X3 ◇ (((X1 ◇ X4) ◇ X5) ◇ X6)) ◇ X3) = X1 := superpose eq29 eq69
  have eq106 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq102 eq31
  have eq107 (X0 X4 : G) : X0 = X4 := superpose eq7 eq106
  have eq225 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq225 eq107


@[equational_result]
theorem Equation38357_implies_Equation2 (G : Type*) [Magma G] (h : Equation38357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X4)) = (((X1 ◇ X0) ◇ X1) ◇ X4) := superpose eq7 eq7
  have eq18 (X0 X3 X5 X6 : G) : (((X6 ◇ X3) ◇ X6) ◇ X5) = X0 := superpose eq7 eq10
  have eq106 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq222 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq222 eq106


@[equational_result]
theorem Equation38358_implies_Equation2 (G : Type*) [Magma G] (h : Equation38358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X6 : G) : (X0 ◇ X6) = X1 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation38360_implies_Equation2 (G : Type*) [Magma G] (h : Equation38360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4))) = X2 := superpose eq7 eq7
  have eq58 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq12
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq58
  have eq202 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq202 eq68


@[equational_result]
theorem Equation38361_implies_Equation2 (G : Type*) [Magma G] (h : Equation38361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation38362_implies_Equation2 (G : Type*) [Magma G] (h : Equation38362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38363_implies_Equation2 (G : Type*) [Magma G] (h : Equation38363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X6 : G) : (X0 ◇ X6) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38365_implies_Equation2 (G : Type*) [Magma G] (h : Equation38365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X4)) = (((X1 ◇ X0) ◇ X2) ◇ X1) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X6 ◇ X1) ◇ ((((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ X4) ◇ X5)) ◇ X5)) ◇ X6) = X0 := superpose eq7 eq10
  have eq24 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X3 ◇ ((((X1 ◇ X4) ◇ X5) ◇ X6) ◇ X7)) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X3) ◇ X2) := superpose eq10 eq10
  have eq31 (X0 X1 X2 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X4) ◇ X2) = X1 := superpose eq10 eq7
  have eq41 (X1 X3 X4 X5 X6 X7 : G) : (X3 ◇ ((((X1 ◇ X4) ◇ X5) ◇ X6) ◇ X7)) = X1 := superpose eq31 eq24
  have eq42 (X0 X1 X6 : G) : (X1 ◇ X6) = X0 := superpose eq41 eq19
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq42
  have eq204 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq204 eq71


@[equational_result]
theorem Equation38366_implies_Equation2 (G : Type*) [Magma G] (h : Equation38366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38367_implies_Equation2 (G : Type*) [Magma G] (h : Equation38367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation38368_implies_Equation2 (G : Type*) [Magma G] (h : Equation38368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38370_implies_Equation2 (G : Type*) [Magma G] (h : Equation38370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq79 eq22


@[equational_result]
theorem Equation38371_implies_Equation2 (G : Type*) [Magma G] (h : Equation38371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38372_implies_Equation2 (G : Type*) [Magma G] (h : Equation38372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38373_implies_Equation2 (G : Type*) [Magma G] (h : Equation38373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X7 : G) : ((X0 ◇ X7) ◇ X7) = X4 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq30 eq18


@[equational_result]
theorem Equation38374_implies_Equation2 (G : Type*) [Magma G] (h : Equation38374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X8 : G) : (X0 ◇ X8) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38377_implies_Equation2 (G : Type*) [Magma G] (h : Equation38377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation38380_implies_Equation2 (G : Type*) [Magma G] (h : Equation38380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq61 eq26


@[equational_result]
theorem Equation38382_implies_Equation2 (G : Type*) [Magma G] (h : Equation38382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation38383_implies_Equation2 (G : Type*) [Magma G] (h : Equation38383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2)) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq11
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq51 eq13


@[equational_result]
theorem Equation38384_implies_Equation2 (G : Type*) [Magma G] (h : Equation38384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation38387_implies_Equation2 (G : Type*) [Magma G] (h : Equation38387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0))) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq12 eq7
  have eq14 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq13
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq14 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation38390_implies_Equation2 (G : Type*) [Magma G] (h : Equation38390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq64 eq27


@[equational_result]
theorem Equation38392_implies_Equation2 (G : Type*) [Magma G] (h : Equation38392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation38394_implies_Equation2 (G : Type*) [Magma G] (h : Equation38394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation38396_implies_Equation2 (G : Type*) [Magma G] (h : Equation38396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X0 ◇ X3)) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0)) := superpose eq7 eq9
  have eq32 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq11 eq11
  have eq39 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = X1 := superpose eq11 eq7
  have eq46 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ X0)) := superpose eq7 eq21
  have eq55 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X0) := superpose eq7 eq46
  have eq56 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq11 eq55
  have eq62 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq56 eq11
  have eq63 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq62 eq32
  have eq64 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq63 eq56
  have eq71 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0)) := superpose eq64 eq21
  have eq74 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq64 eq39
  have eq76 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq74 eq71
  have eq128 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X0) := superpose eq7 eq64
  have eq138 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) = X0 := superpose eq64 eq76
  have eq139 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) := superpose eq64 eq76
  have eq165 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq74 eq138
  have eq180 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq165 eq128
  have eq193 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq180 eq139
  have eq194 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq165 eq193
  have eq207 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq194 eq74
  have eq238 (X0 X2 : G) : X0 = X2 := superpose eq207 eq207
  have eq243 (X0 : G) : sK0 ≠ X0 := superpose eq238 eq8
  subsumption eq243 eq238


@[equational_result]
theorem Equation38397_implies_Equation2 (G : Type*) [Magma G] (h : Equation38397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X0 ◇ X3)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq10
  have eq32 (X0 X1 X2 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq15 eq9
  have eq39 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq10 eq32
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq39 eq39
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq122 eq56


@[equational_result]
theorem Equation38398_implies_Equation2 (G : Type*) [Magma G] (h : Equation38398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X0 ◇ X4)) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = X0 := superpose eq12 eq7
  have eq14 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq12 eq13
  have eq15 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq14 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation38400_implies_Equation2 (G : Type*) [Magma G] (h : Equation38400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = ((((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X1) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X3)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq10 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2)) ◇ X4)) ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2)) ◇ X4)) ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2)) ◇ X4)) ◇ X1)) = X1 := superpose eq7 eq9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) = (((((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ X5)) ◇ ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)))) ◇ ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)))) := superpose eq9 eq9
  have eq31 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2)))) := superpose eq7 eq20
  have eq40 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq20 eq7
  have eq44 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) = ((((X0 ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)))) := superpose eq20 eq7
  have eq48 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) := superpose eq40 eq20
  have eq52 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = ((((X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))) := superpose eq40 eq44
  have eq54 (X0 X1 X2 : G) : (((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) ◇ ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) = X0 := superpose eq10 eq48
  have eq64 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = (((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X1) ◇ X1) := superpose eq7 eq40
  have eq65 (X0 X1 X2 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) = ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq10 eq40
  have eq70 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) ◇ X4)) ◇ X0) = (((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ X0) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) := superpose eq9 eq40
  have eq72 (X0 X1 X3 : G) : (X0 ◇ X1) = ((((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ (X0 ◇ X3)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) := superpose eq40 eq9
  have eq73 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq40 eq7
  have eq76 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq40 eq7
  have eq77 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)))) ◇ (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)))) := superpose eq40 eq48
  have eq84 (X0 X1 X2 : G) : ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) = X0 := superpose eq76 eq54
  have eq85 (X0 X1 X2 : G) : ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) = X0 := superpose eq65 eq84
  have eq86 (X0 X1 X2 : G) : (X0 ◇ ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) = X0 := superpose eq7 eq85
  have eq117 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = (((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X0) := superpose eq10 eq73
  have eq124 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) := superpose eq73 eq10
  have eq131 (X0 X1 X2 : G) : ((((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ X2)) ◇ X0) := superpose eq73 eq40
  have eq133 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ X2)) ◇ X0) := superpose eq124 eq131
  have eq138 (X0 X1 X2 X3 X4 X5 : G) : ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) = ((((((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ X5)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) ◇ (((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ X5))) ◇ (((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ X5))) := superpose eq9 eq11
  have eq152 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2)) ◇ X4)) ◇ X1) = ((((((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2)) ◇ X4)) ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2)) ◇ X4)) ◇ X1) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2)) ◇ X4)) ◇ X1) ◇ X0)) := superpose eq7 eq11
  have eq179 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)))) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := superpose eq40 eq133
  have eq180 (X0 X1 X2 X3 : G) : (((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = (((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) ◇ X3)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq10 eq133
  have eq209 (X0 X1 X2 : G) : (((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq76 eq180
  have eq210 (X0 X1 X2 : G) : (((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = ((((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq65 eq209
  have eq211 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) = (((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq7 eq210
  have eq212 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = (((X0 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ X0) := superpose eq211 eq117
  have eq213 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) = X0 := superpose eq211 eq86
  have eq215 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq31 eq212
  have eq218 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) := superpose eq215 eq16
  have eq221 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = ((X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) := superpose eq215 eq31
  have eq223 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = (((X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X1) ◇ X1) := superpose eq215 eq64
  have eq259 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0))) = X0 := superpose eq215 eq213
  have eq260 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq221 eq259
  have eq261 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq260 eq223
  have eq262 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose eq261 eq7
  have eq263 (X0 X1 X3 : G) : (((((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq261 eq9
  have eq264 (X0 X1 X2 X4 : G) : (((((X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X4)) ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X4)) ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X4)) ◇ X1)) = X1 := superpose eq261 eq17
  have eq267 (X0 X1 X3 X4 X5 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) = (((((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X5)) ◇ ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq261 eq23
  have eq270 (X0 X1 X3 X4 : G) : ((X0 ◇ ((X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X4)) ◇ X0) = (((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq261 eq70
  have eq274 (X0 X1 X3 X4 X5 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) = ((((((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X5)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X5))) ◇ (((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ X5))) := superpose eq261 eq138
  have eq276 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X4)) ◇ X1) = ((((((X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X4)) ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X4)) ◇ X1) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X4)) ◇ X1) ◇ X0)) := superpose eq261 eq152
  have eq284 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq261 eq218
  have eq327 (X0 X1 : G) : (((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq261 eq264
  have eq329 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X0) = (((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq261 eq270
  have eq331 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) := superpose eq261 eq276
  have eq333 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq263 eq284
  have eq334 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) := superpose eq333 eq179
  have eq336 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq333 eq77
  have eq362 (X0 X1 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq333 eq334
  have eq364 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq362 eq76
  have eq370 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq362 eq336
  have eq371 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq333 eq370
  have eq372 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq333 eq371
  have eq373 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq372 eq48
  have eq376 (X0 X1 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq372 eq52
  have eq378 (X0 X1 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq372 eq72
  have eq379 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq372 eq73
  have eq402 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (X0 ◇ (X0 ◇ X1)) := superpose eq379 eq364
  have eq404 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq402 eq329
  have eq405 (X1 : G) : ((X1 ◇ X1) ◇ X1) = ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq402 eq331
  have eq406 (X0 X1 X3 X4 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) = ((((((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq402 eq274
  have eq407 (X0 X1 X3 X4 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) = (((((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq402 eq267
  have eq408 (X1 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq402 eq327
  have eq421 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq402 eq404
  have eq422 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq402 eq421
  have eq423 (X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq402 eq405
  have eq424 (X1 : G) : ((X1 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ X1)) := superpose eq373 eq423
  have eq425 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X1) = X0 := superpose eq424 eq262
  have eq426 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq424 eq422
  have eq427 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq379 eq426
  have eq428 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq372 eq427
  have eq429 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq428 eq425
  have eq431 (X0 X1 X3 X4 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) = ((((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)))) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)))) := superpose eq402 eq406
  have eq432 (X0 X1 X3 X4 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) = ((((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)))) := superpose eq402 eq431
  have eq433 (X0 X1 X3 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) = ((((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq376 eq432
  have eq434 (X0 X4 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq402 eq433
  have eq435 (X0 X4 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq428 eq434
  have eq436 (X0 X4 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (((((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq402 eq407
  have eq437 (X0 X4 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X4)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq428 eq436
  have eq438 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq435 eq437
  have eq439 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq378 eq438
  have eq441 (X1 : G) : (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq428 eq408
  have eq442 (X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = X1 := superpose eq439 eq441
  have eq443 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq442 eq439
  have eq446 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq443 eq429
  have eq854 (X0 X2 : G) : X0 = X2 := superpose eq446 eq446
  have eq856 (X0 : G) : sK0 ≠ X0 := superpose eq854 eq8
  subsumption eq856 eq854


@[equational_result]
theorem Equation38401_implies_Equation2 (G : Type*) [Magma G] (h : Equation38401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X2) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = ((((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) ◇ X2) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ X3))) ◇ X3) := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) ◇ X2) := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ ((X1 ◇ (((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ X4)) ◇ X1) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ (((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ X4)) ◇ X1)) ◇ X3) = X4 := superpose eq10 eq9
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X1)) ◇ X2) := superpose eq7 eq9
  have eq42 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq20 eq7
  have eq45 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq20 eq7
  have eq61 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ X2)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ X2))) ◇ X1) := superpose eq20 eq13
  have eq74 (X0 X1 : G) : (X0 ◇ X0) = (((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) ◇ X1) := superpose eq42 eq9
  have eq94 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq74
  have eq114 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = ((X0 ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq10 eq11
  have eq127 (X0 X1 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1))) ◇ X1) := superpose eq20 eq11
  have eq146 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) := superpose eq94 eq114
  have eq147 (X0 X1 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) ◇ X1) := superpose eq94 eq127
  have eq148 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := superpose eq94 eq147
  have eq149 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X0 := superpose eq94 eq7
  have eq164 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ X2) = X0 := superpose eq149 eq45
  have eq175 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq164 eq61
  have eq240 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq149 eq149
  have eq258 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq175 eq240
  have eq260 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) := superpose eq258 eq146
  have eq261 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) = X0 := superpose eq258 eq148
  have eq274 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq94 eq260
  have eq275 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq94 eq261
  have eq278 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq275 eq274
  have eq282 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq278 eq275
  have eq283 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X1 ◇ (((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ X4)) ◇ X1) ◇ X0) ◇ X3) = X4 := superpose eq282 eq18
  have eq380 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ (((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ X4)) ◇ X1) ◇ X3) = X4 := superpose eq282 eq283
  have eq381 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) ◇ X4)) ◇ X3) = X4 := superpose eq282 eq380
  have eq382 (X1 X3 X4 : G) : (X1 ◇ X3) = X4 := superpose eq282 eq381
  have eq383 (X0 X1 : G) : X0 = X1 := superpose eq94 eq382
  have eq388 (X0 : G) : sK0 ≠ X0 := superpose eq383 eq8
  subsumption eq388 eq383


@[equational_result]
theorem Equation38402_implies_Equation2 (G : Type*) [Magma G] (h : Equation38402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) ◇ (X0 ◇ X4)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq9
  have eq27 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq64 eq27


@[equational_result]
theorem Equation38404_implies_Equation2 (G : Type*) [Magma G] (h : Equation38404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := superpose eq7 eq10
  have eq12 (X0 X1 X2 X3 : G) : ((((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ (X0 ◇ X3))) = X3 := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X2) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0)) = X1 := superpose eq7 eq10
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = ((((((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) ◇ X3) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ X1)) := superpose eq10 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X0) ◇ X2) ◇ ((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4)) = X1 := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2)) := superpose eq7 eq9
  have eq36 (X0 X1 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq11
  have eq42 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = X2 := superpose eq11 eq10
  have eq43 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0) := superpose eq11 eq7
  have eq53 (X0 X2 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2)) = X0 := superpose eq11 eq21
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2)))) := superpose eq21 eq11
  have eq73 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq21 eq65
  have eq115 (X0 X1 X2 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose eq11 eq14
  have eq226 (X0 X1 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq53 eq14
  have eq229 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq53 eq7
  have eq249 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq7 eq226
  have eq301 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X0)) = ((((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X0)) := superpose eq11 eq12
  have eq302 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X3) = ((((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X0)) := superpose eq36 eq12
  have eq368 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X0) = X0 := superpose eq229 eq7
  have eq457 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2) ◇ X0) = (((((((((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2) ◇ X0) ◇ X1) ◇ (((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2)) ◇ (((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X5)) ◇ X5) ◇ ((((((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2) ◇ X0) ◇ X1) ◇ (((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2))) := superpose eq18 eq17
  have eq486 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq249
  have eq516 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq486 eq73
  have eq619 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2) = X0 := superpose eq7 eq516
  have eq620 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq619 eq21
  have eq655 (X0 X1 X2 X3 : G) : ((((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X0)) = ((X0 ◇ (X0 ◇ X3)) ◇ X3) := superpose eq620 eq302
  have eq658 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = X0 := superpose eq620 eq368
  have eq670 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq658 eq43
  have eq678 (X0 X2 : G) : ((((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = X2 := superpose eq670 eq42
  have eq683 (X0 X1 X2 : G) : ((((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X0) ◇ X1) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X0)) = X0 := superpose eq670 eq301
  have eq688 (X0 X1 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := superpose eq670 eq115
  have eq692 (X0 X2 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = X2 := superpose eq620 eq678
  have eq693 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2))) = X2 := superpose eq620 eq692
  have eq698 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X3) = X0 := superpose eq683 eq655
  have eq736 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X0 := superpose eq698 eq688
  have eq737 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq693 eq736
  have eq738 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2) ◇ X0) = ((((((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2) ◇ (((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X5)) ◇ X5) ◇ (((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2)) := superpose eq737 eq457
  have eq882 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2) = ((((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2) ◇ X0) := superpose eq737 eq738
  have eq883 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3)) ◇ X4)) ◇ X4) ◇ X2) = X0 := superpose eq737 eq882
  have eq884 (X0 X2 X4 : G) : (X4 ◇ X2) = X0 := superpose eq737 eq883
  have eq885 (X0 X3 : G) : X0 = X3 := superpose eq884 eq884
  have eq890 (X0 : G) : sK0 ≠ X0 := superpose eq885 eq8
  subsumption eq890 eq885


@[equational_result]
theorem Equation38405_implies_Equation2 (G : Type*) [Magma G] (h : Equation38405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X2) ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq7 eq10
  have eq18 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq10 eq13
  have eq29 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ ((X1 ◇ (((X2 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) ◇ X0)) ◇ X4)) ◇ X4) ◇ X0) ◇ X0) ◇ X0) = X4 := superpose eq10 eq9
  have eq31 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ X2) := superpose eq7 eq9
  have eq37 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X1 ◇ (((X2 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) ◇ X0)) ◇ X4)) ◇ X4) ◇ X0) ◇ X0) = X4 := superpose eq31 eq29
  have eq49 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq31
  have eq70 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0)) ◇ X4)) ◇ X4) ◇ X0) ◇ X0) = X4 := superpose eq49 eq37
  have eq93 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0)) ◇ X4)) ◇ X4) ◇ X0) = X4 := superpose eq49 eq70
  have eq94 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0)) ◇ X4)) ◇ X0) = X4 := superpose eq49 eq93
  have eq95 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq49 eq94
  have eq96 (X0 X1 : G) : X0 = X1 := superpose eq18 eq95
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq101 eq96


@[equational_result]
theorem Equation38406_implies_Equation2 (G : Type*) [Magma G] (h : Equation38406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ (X0 ◇ X4)) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X3 := superpose eq7 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq29 eq16


@[equational_result]
theorem Equation38408_implies_Equation2 (G : Type*) [Magma G] (h : Equation38408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq69 eq20


@[equational_result]
theorem Equation38409_implies_Equation2 (G : Type*) [Magma G] (h : Equation38409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq61 eq12


@[equational_result]
theorem Equation38410_implies_Equation2 (G : Type*) [Magma G] (h : Equation38410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X4) ◇ X4) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq55 eq22


@[equational_result]
theorem Equation38411_implies_Equation2 (G : Type*) [Magma G] (h : Equation38411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation38414_implies_Equation2 (G : Type*) [Magma G] (h : Equation38414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq13
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq21 eq14


@[equational_result]
theorem Equation38417_implies_Equation2 (G : Type*) [Magma G] (h : Equation38417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq33 eq23


@[equational_result]
theorem Equation38419_implies_Equation2 (G : Type*) [Magma G] (h : Equation38419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq44 eq17


@[equational_result]
theorem Equation38421_implies_Equation2 (G : Type*) [Magma G] (h : Equation38421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation38424_implies_Equation2 (G : Type*) [Magma G] (h : Equation38424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0))) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ X2) = X0 := superpose eq13 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq14
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38426_implies_Equation2 (G : Type*) [Magma G] (h : Equation38426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation38427_implies_Equation2 (G : Type*) [Magma G] (h : Equation38427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38429_implies_Equation2 (G : Type*) [Magma G] (h : Equation38429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38430_implies_Equation2 (G : Type*) [Magma G] (h : Equation38430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38431_implies_Equation2 (G : Type*) [Magma G] (h : Equation38431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38433_implies_Equation2 (G : Type*) [Magma G] (h : Equation38433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq7 eq9
  have eq12 (X0 X1 X2 : G) : (((((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) ◇ X2) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := superpose eq11 eq10
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X2 := superpose eq11 eq9
  have eq18 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq11 eq12
  have eq20 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) = (X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) ◇ ((((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0)) ◇ X3))) := superpose eq7 eq16
  have eq26 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq16 eq7
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) = (X0 ◇ (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0))) := superpose eq26 eq20
  have eq33 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq26 eq17
  have eq36 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq26 eq28
  have eq42 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose eq18 eq33
  have eq43 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq42 eq36
  have eq44 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq43 eq18
  have eq48 (X0 X1 : G) : X0 = X1 := superpose eq33 eq44
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq66 eq48


@[equational_result]
theorem Equation38435_implies_Equation2 (G : Type*) [Magma G] (h : Equation38435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X0) ◇ (X0 ◇ X3)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq13 eq7
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq14
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38437_implies_Equation2 (G : Type*) [Magma G] (h : Equation38437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation38438_implies_Equation2 (G : Type*) [Magma G] (h : Equation38438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation38439_implies_Equation2 (G : Type*) [Magma G] (h : Equation38439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38441_implies_Equation2 (G : Type*) [Magma G] (h : Equation38441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation38442_implies_Equation2 (G : Type*) [Magma G] (h : Equation38442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation38443_implies_Equation2 (G : Type*) [Magma G] (h : Equation38443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38445_implies_Equation2 (G : Type*) [Magma G] (h : Equation38445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38446_implies_Equation2 (G : Type*) [Magma G] (h : Equation38446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38447_implies_Equation2 (G : Type*) [Magma G] (h : Equation38447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38448_implies_Equation2 (G : Type*) [Magma G] (h : Equation38448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38450_implies_Equation2 (G : Type*) [Magma G] (h : Equation38450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq11 eq11
  have eq18 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X3)) ◇ X3) ◇ X1) = X3 := superpose eq11 eq7
  have eq45 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq13
  have eq70 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq45 eq7
  have eq73 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X1) = X3 := superpose eq45 eq18
  have eq79 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq73 eq70
  have eq82 (X0 X3 : G) : X0 = X3 := superpose eq79 eq79
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq84 eq82


@[equational_result]
theorem Equation38451_implies_Equation2 (G : Type*) [Magma G] (h : Equation38451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq10
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation38452_implies_Equation2 (G : Type*) [Magma G] (h : Equation38452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ X4)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation38454_implies_Equation2 (G : Type*) [Magma G] (h : Equation38454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq9
  have eq44 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := superpose eq20 eq7
  have eq53 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X1 := superpose eq44 eq20
  have eq62 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq53
  have eq72 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose eq62 eq7
  have eq126 (X0 X2 : G) : X0 = X2 := superpose eq72 eq72
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq126 eq8
  subsumption eq135 eq126


@[equational_result]
theorem Equation38456_implies_Equation2 (G : Type*) [Magma G] (h : Equation38456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) ◇ (X0 ◇ X4)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) ◇ X5) = X4 := superpose eq7 eq9
  have eq27 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq81 eq27


@[equational_result]
theorem Equation38460_implies_Equation2 (G : Type*) [Magma G] (h : Equation38460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) ◇ (X0 ◇ X4)) ◇ X3) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ X5) = X4 := superpose eq7 eq9
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq29 eq16


@[equational_result]
theorem Equation38462_implies_Equation2 (G : Type*) [Magma G] (h : Equation38462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) = X4 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq53 eq20


@[equational_result]
theorem Equation38463_implies_Equation2 (G : Type*) [Magma G] (h : Equation38463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq50 eq12


@[equational_result]
theorem Equation38464_implies_Equation2 (G : Type*) [Magma G] (h : Equation38464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X4) ◇ X4) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq55 eq22


@[equational_result]
theorem Equation38465_implies_Equation2 (G : Type*) [Magma G] (h : Equation38465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation38467_implies_Equation2 (G : Type*) [Magma G] (h : Equation38467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) = ((((((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0))) ◇ X3) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)))) ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)))) := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = (((((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))))) ◇ X3) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))))) ◇ ((((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ (X0 ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))))) := superpose eq10 eq10
  have eq14 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq7 eq10
  have eq18 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = ((((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) ◇ X3) ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0)))) ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0)))) := superpose eq14 eq13
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = (((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq14 eq12
  have eq20 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq14 eq10
  have eq22 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq14 eq7
  have eq24 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = ((((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ X3) ◇ (((X0 ◇ X2) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X2) ◇ X0) ◇ X0)) := superpose eq14 eq18
  have eq25 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = (((X0 ◇ X3) ◇ X0) ◇ X0) := superpose eq20 eq24
  have eq27 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X0 := superpose eq20 eq25
  have eq28 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq27 eq20
  have eq30 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq27 eq19
  have eq34 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq22 eq22
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq34 eq30
  have eq37 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq28 eq36
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq37 eq34
  have eq43 (X0 X2 : G) : X0 = X2 := superpose eq39 eq39
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq48 eq43


@[equational_result]
theorem Equation38469_implies_Equation2 (G : Type*) [Magma G] (h : Equation38469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0))) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq13 eq7
  have eq15 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq13 eq14
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38471_implies_Equation2 (G : Type*) [Magma G] (h : Equation38471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38472_implies_Equation2 (G : Type*) [Magma G] (h : Equation38472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38473_implies_Equation2 (G : Type*) [Magma G] (h : Equation38473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38475_implies_Equation2 (G : Type*) [Magma G] (h : Equation38475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38476_implies_Equation2 (G : Type*) [Magma G] (h : Equation38476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38477_implies_Equation2 (G : Type*) [Magma G] (h : Equation38477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38479_implies_Equation2 (G : Type*) [Magma G] (h : Equation38479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38480_implies_Equation2 (G : Type*) [Magma G] (h : Equation38480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38481_implies_Equation2 (G : Type*) [Magma G] (h : Equation38481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38482_implies_Equation2 (G : Type*) [Magma G] (h : Equation38482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38486_implies_Equation2 (G : Type*) [Magma G] (h : Equation38486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) ◇ (X0 ◇ X3)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X3) = X0 := superpose eq13 eq7
  have eq15 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq13 eq14
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38488_implies_Equation2 (G : Type*) [Magma G] (h : Equation38488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38489_implies_Equation2 (G : Type*) [Magma G] (h : Equation38489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38490_implies_Equation2 (G : Type*) [Magma G] (h : Equation38490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38492_implies_Equation2 (G : Type*) [Magma G] (h : Equation38492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38493_implies_Equation2 (G : Type*) [Magma G] (h : Equation38493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38494_implies_Equation2 (G : Type*) [Magma G] (h : Equation38494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38496_implies_Equation2 (G : Type*) [Magma G] (h : Equation38496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38497_implies_Equation2 (G : Type*) [Magma G] (h : Equation38497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38498_implies_Equation2 (G : Type*) [Magma G] (h : Equation38498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38499_implies_Equation2 (G : Type*) [Magma G] (h : Equation38499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38501_implies_Equation2 (G : Type*) [Magma G] (h : Equation38501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) ◇ X4) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ X4) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq7 eq7
  have eq35 (X0 X1 : G) : X0 = X1 := superpose eq10 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq47 eq35


@[equational_result]
theorem Equation38502_implies_Equation2 (G : Type*) [Magma G] (h : Equation38502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ X4) ◇ X3) = X1 := superpose eq7 eq7
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq10 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq45 eq35


@[equational_result]
theorem Equation38503_implies_Equation2 (G : Type*) [Magma G] (h : Equation38503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) ◇ X4) ◇ X3) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ X4) ◇ X4) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq7 eq10
  have eq31 (X2 X4 : G) : (X4 ◇ X4) = X2 := superpose eq18 eq11
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq39 eq37


@[equational_result]
theorem Equation38504_implies_Equation2 (G : Type*) [Magma G] (h : Equation38504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) ◇ (X0 ◇ X5)) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq13 eq7
  have eq15 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq13 eq14
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38506_implies_Equation2 (G : Type*) [Magma G] (h : Equation38506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38507_implies_Equation2 (G : Type*) [Magma G] (h : Equation38507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38508_implies_Equation2 (G : Type*) [Magma G] (h : Equation38508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38509_implies_Equation2 (G : Type*) [Magma G] (h : Equation38509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38511_implies_Equation2 (G : Type*) [Magma G] (h : Equation38511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38512_implies_Equation2 (G : Type*) [Magma G] (h : Equation38512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38513_implies_Equation2 (G : Type*) [Magma G] (h : Equation38513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38514_implies_Equation2 (G : Type*) [Magma G] (h : Equation38514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38516_implies_Equation2 (G : Type*) [Magma G] (h : Equation38516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38517_implies_Equation2 (G : Type*) [Magma G] (h : Equation38517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38518_implies_Equation2 (G : Type*) [Magma G] (h : Equation38518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38519_implies_Equation2 (G : Type*) [Magma G] (h : Equation38519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38521_implies_Equation2 (G : Type*) [Magma G] (h : Equation38521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38522_implies_Equation2 (G : Type*) [Magma G] (h : Equation38522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38523_implies_Equation2 (G : Type*) [Magma G] (h : Equation38523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38524_implies_Equation2 (G : Type*) [Magma G] (h : Equation38524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38525_implies_Equation2 (G : Type*) [Magma G] (h : Equation38525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38527_implies_Equation2 (G : Type*) [Magma G] (h : Equation38527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X0) ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq9
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) = X1 := superpose eq7 eq9
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X1 := superpose eq9 eq9
  have eq30 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq10
  have eq36 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq16 eq9
  have eq43 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X0) ◇ X0) ◇ ((X3 ◇ X1) ◇ X1)) ◇ X1) = (X0 ◇ ((((X4 ◇ ((((X2 ◇ X0) ◇ X0) ◇ ((X3 ◇ X1) ◇ X1)) ◇ X1)) ◇ ((((X2 ◇ X0) ◇ X0) ◇ ((X3 ◇ X1) ◇ X1)) ◇ X1)) ◇ ((X5 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) := superpose eq11 eq11
  have eq68 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq36 eq10
  have eq125 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq9 eq21
  have eq154 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = X1 := superpose eq125 eq27
  have eq155 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq125 eq28
  have eq161 (X0 X1 X3 X4 X5 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ ((((X4 ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X3 ◇ X1) ◇ X1)) ◇ ((X5 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) := superpose eq155 eq43
  have eq187 (X0 X1 X3 X5 : G) : ((X3 ◇ X1) ◇ X1) = (X0 ◇ ((X5 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq155 eq161
  have eq188 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X3 ◇ X1) ◇ X1) := superpose eq155 eq187
  have eq189 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq155 eq188
  have eq190 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq189 eq30
  have eq193 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq190 eq154
  have eq199 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq190 eq193
  have eq200 (X0 X1 : G) : X0 = X1 := superpose eq68 eq199
  have eq208 (X0 : G) : sK0 ≠ X0 := superpose eq200 eq8
  subsumption eq208 eq200


@[equational_result]
theorem Equation38528_implies_Equation2 (G : Type*) [Magma G] (h : Equation38528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq35 eq23


@[equational_result]
theorem Equation38529_implies_Equation2 (G : Type*) [Magma G] (h : Equation38529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ X4) = X0 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq11 eq10
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq15 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation38531_implies_Equation2 (G : Type*) [Magma G] (h : Equation38531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation38533_implies_Equation2 (G : Type*) [Magma G] (h : Equation38533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation38536_implies_Equation2 (G : Type*) [Magma G] (h : Equation38536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation38537_implies_Equation2 (G : Type*) [Magma G] (h : Equation38537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38539_implies_Equation2 (G : Type*) [Magma G] (h : Equation38539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation38540_implies_Equation2 (G : Type*) [Magma G] (h : Equation38540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38541_implies_Equation2 (G : Type*) [Magma G] (h : Equation38541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq34 eq16


@[equational_result]
theorem Equation38542_implies_Equation2 (G : Type*) [Magma G] (h : Equation38542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38544_implies_Equation2 (G : Type*) [Magma G] (h : Equation38544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq17 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq7 eq9
  have eq27 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq14 eq9
  have eq32 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq14 eq9
  have eq33 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq27 eq32
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq10 eq17
  have eq40 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X1 := superpose eq9 eq17
  have eq51 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq40 eq33
  have eq53 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq51 eq36
  have eq71 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq51 eq53
  have eq82 (X0 X1 : G) : X0 = X1 := superpose eq51 eq71
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq82 eq8
  subsumption eq84 eq82


@[equational_result]
theorem Equation38545_implies_Equation2 (G : Type*) [Magma G] (h : Equation38545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq10
  have eq18 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq10 eq7
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X4)) ◇ X0) = (((X1 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X3) ◇ X1)) ◇ ((X4 ◇ (X3 ◇ X4)) ◇ X0)) ◇ ((X5 ◇ (X0 ◇ X5)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X3))) := superpose eq9 eq9
  have eq54 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ X3))) = X2 := superpose eq7 eq12
  have eq56 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) := superpose eq10 eq12
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) = X1 := superpose eq18 eq12
  have eq83 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq57 eq56
  have eq97 (X0 X1 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X4)) ◇ X0) = (((X1 ◇ ((X0 ◇ X3) ◇ X1)) ◇ ((X4 ◇ (X3 ◇ X4)) ◇ X0)) ◇ ((X5 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X3))) := superpose eq83 eq26
  have eq102 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X3))) = X2 := superpose eq83 eq54
  have eq113 (X0 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X4)) ◇ X0) = ((X0 ◇ ((X4 ◇ (X3 ◇ X4)) ◇ X0)) ◇ ((X5 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X3))) := superpose eq83 eq97
  have eq114 (X0 X3 X4 X5 : G) : ((X4 ◇ (X3 ◇ X4)) ◇ X0) = (X4 ◇ ((X5 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X3))) := superpose eq83 eq113
  have eq115 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq83 eq102
  have eq127 (X0 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X3))) = X0 := superpose eq115 eq114
  have eq143 (X0 X3 X4 : G) : (X4 ◇ (X0 ◇ X3)) = X0 := superpose eq115 eq127
  have eq144 (X0 X3 X4 : G) : (X4 ◇ X3) = X0 := superpose eq115 eq143
  have eq145 (X0 X3 : G) : X0 = X3 := superpose eq144 eq144
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq145 eq8
  subsumption eq150 eq145


@[equational_result]
theorem Equation38546_implies_Equation2 (G : Type*) [Magma G] (h : Equation38546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq11 eq12
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq15 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation38548_implies_Equation2 (G : Type*) [Magma G] (h : Equation38548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq40 eq13


@[equational_result]
theorem Equation38549_implies_Equation2 (G : Type*) [Magma G] (h : Equation38549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X2)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq7 eq7
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = (((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) := superpose eq9 eq10
  have eq42 (X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq34
  have eq43 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq42 eq7
  have eq44 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X3 ◇ X0)) = X3 := superpose eq42 eq9
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq43 eq10
  have eq66 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq42 eq44
  have eq67 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq66 eq42
  have eq69 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq66 eq64
  have eq76 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq67 eq69
  have eq77 (X0 X3 : G) : X0 = X3 := superpose eq76 eq76
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq82 eq77


@[equational_result]
theorem Equation38550_implies_Equation2 (G : Type*) [Magma G] (h : Equation38550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ X4) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation38553_implies_Equation2 (G : Type*) [Magma G] (h : Equation38553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X3)) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X3)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X2) = ((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq7 eq10
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq10 eq10
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ (X3 ◇ X5)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0)) = (((X1 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0) ◇ X1)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ ((X5 ◇ (X3 ◇ X5)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0)))) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ ((X5 ◇ (X3 ◇ X5)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0)))) := superpose eq9 eq9
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))) = (((X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X1)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ ((X0 ◇ X3) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))))) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ ((X0 ◇ X3) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))))) := superpose eq10 eq9
  have eq28 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0)) = ((X0 ◇ (X4 ◇ (X0 ◇ X4))) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq9 eq10
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ ((X4 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X0))) = ((((X4 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X0) ◇ (X5 ◇ (((X4 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X0) ◇ X5))) ◇ (X5 ◇ (((X4 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X0) ◇ X5))) := superpose eq9 eq11
  have eq68 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ X3) ◇ X4)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ ((X4 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X0))) := superpose eq10 eq35
  have eq69 (X0 X1 X2 X3 X5 : G) : ((X5 ◇ (X3 ◇ X5)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0)) = (((X1 ◇ (((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0) ◇ X1)) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))) := superpose eq68 eq21
  have eq71 (X0 X2 X3 X5 : G) : ((X5 ◇ (X3 ◇ X5)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0)) = X0 := superpose eq7 eq69
  have eq73 (X0 X4 : G) : ((X0 ◇ (X4 ◇ (X0 ◇ X4))) ◇ (X4 ◇ (X0 ◇ X4))) = X0 := superpose eq71 eq28
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq73 eq12
  have eq78 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X2) = X0 := superpose eq73 eq11
  have eq79 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X1)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ X0)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ X0)) = X0 := superpose eq77 eq22
  have eq84 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq78 eq7
  have eq93 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X1)) ◇ (X4 ◇ (X0 ◇ X4))) ◇ (X4 ◇ (X0 ◇ X4))) = X0 := superpose eq84 eq79
  have eq102 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X1)) ◇ X4) ◇ X4) = X0 := superpose eq84 eq93
  have eq103 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X1)) ◇ X4) = X0 := superpose eq84 eq102
  have eq104 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq84 eq103
  have eq105 (X0 X3 : G) : X0 = X3 := superpose eq104 eq104
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq124 eq105


@[equational_result]
theorem Equation38554_implies_Equation2 (G : Type*) [Magma G] (h : Equation38554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation38556_implies_Equation2 (G : Type*) [Magma G] (h : Equation38556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X1) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation38557_implies_Equation2 (G : Type*) [Magma G] (h : Equation38557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation38558_implies_Equation2 (G : Type*) [Magma G] (h : Equation38558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X4) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation38559_implies_Equation2 (G : Type*) [Magma G] (h : Equation38559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38561_implies_Equation2 (G : Type*) [Magma G] (h : Equation38561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X0))) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X1) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ ((X2 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X0))) ◇ X2))) ◇ X3) ◇ X1) = X3 := superpose eq7 eq9
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) ◇ (X1 ◇ ((X3 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0))) ◇ X3))) = X1 := superpose eq7 eq9
  have eq25 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X3 ◇ X1) ◇ X3) ◇ ((X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) ◇ X4)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0))) = X1 := superpose eq7 eq10
  have eq47 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq11 eq9
  have eq48 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ X3) ◇ ((((X4 ◇ X3) ◇ X4) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)))) = X3 := superpose eq11 eq10
  have eq53 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0))) = X1 := superpose eq7 eq47
  have eq57 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq47 eq47
  have eq58 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq47 eq11
  have eq60 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq47 eq7
  have eq73 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq60 eq47
  have eq75 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq73 eq58
  have eq80 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (X2 ◇ ((X3 ◇ (((((X4 ◇ X0) ◇ X4) ◇ ((X5 ◇ X6) ◇ X5)) ◇ X6) ◇ ((X2 ◇ (X0 ◇ (X6 ◇ X0))) ◇ ((((X4 ◇ X0) ◇ X4) ◇ ((X5 ◇ X6) ◇ X5)) ◇ X6)))) ◇ X2))) ◇ X3) ◇ X1) = X3 := superpose eq10 eq12
  have eq124 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (((((X2 ◇ X0) ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X1) ◇ ((((X2 ◇ X0) ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X1))) := superpose eq10 eq75
  have eq127 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq75 eq75
  have eq128 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) := superpose eq60 eq75
  have eq129 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq75 eq7
  have eq136 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := superpose eq75 eq11
  have eq139 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) := superpose eq75 eq7
  have eq153 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := superpose eq127 eq57
  have eq171 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq128 eq139
  have eq172 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq127 eq171
  have eq173 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq172 eq153
  have eq175 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((((X2 ◇ X0) ◇ X2) ◇ ((X3 ◇ X1) ◇ X3)) ◇ X1)) := superpose eq172 eq124
  have eq179 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq172 eq47
  have eq180 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0))) = X1 := superpose eq172 eq53
  have eq209 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ X3) ◇ ((((X4 ◇ X3) ◇ X4) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)))) = X3 := superpose eq179 eq48
  have eq217 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq179 eq136
  have eq221 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq217 eq173
  have eq229 (X0 X2 X3 X4 : G) : (((X0 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) ◇ ((((X4 ◇ X3) ◇ X4) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) = X3 := superpose eq221 eq209
  have eq233 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X3 ◇ X1) ◇ X3) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0))) = X1 := superpose eq221 eq25
  have eq238 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)))) = X1 := superpose eq221 eq20
  have eq262 (X0 X1 X2 X3 X5 X6 : G) : (((X1 ◇ (X2 ◇ ((X3 ◇ (((X0 ◇ ((X5 ◇ X6) ◇ X5)) ◇ X6) ◇ ((X2 ◇ (X0 ◇ (X6 ◇ X0))) ◇ ((X0 ◇ ((X5 ◇ X6) ◇ X5)) ◇ X6)))) ◇ X2))) ◇ X3) ◇ X1) = X3 := superpose eq221 eq80
  have eq288 (X0 X1 X3 : G) : ((X0 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X1)) := superpose eq221 eq175
  have eq313 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ X3) ◇ ((((X4 ◇ X3) ◇ X4) ◇ X0) ◇ (X0 ◇ X0))) = X3 := superpose eq221 eq229
  have eq314 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ ((((X4 ◇ X3) ◇ X4) ◇ X0) ◇ X0)) = X3 := superpose eq172 eq313
  have eq315 (X0 X3 : G) : ((X0 ◇ X3) ◇ ((X3 ◇ X0) ◇ X0)) = X3 := superpose eq221 eq314
  have eq323 (X0 X1 X3 : G) : (X0 ◇ ((((X3 ◇ X1) ◇ X3) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq221 eq233
  have eq324 (X0 X1 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq221 eq323
  have eq332 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := superpose eq221 eq238
  have eq353 (X0 X1 X2 X3 X6 : G) : (((X1 ◇ (X2 ◇ ((X3 ◇ (((X0 ◇ X6) ◇ X6) ◇ ((X2 ◇ (X0 ◇ (X6 ◇ X0))) ◇ ((X0 ◇ X6) ◇ X6)))) ◇ X2))) ◇ X3) ◇ X1) = X3 := superpose eq221 eq262
  have eq375 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq221 eq288
  have eq391 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq221 eq180
  have eq397 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = X1 := superpose eq391 eq332
  have eq461 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq397 eq397
  have eq465 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq172 eq461
  have eq466 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq172 eq465
  have eq467 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq391 eq466
  have eq560 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := superpose eq315 eq221
  have eq567 (X0 X1 : G) : (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) = X1 := superpose eq560 eq324
  have eq569 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq129 eq567
  have eq570 (X0 X1 X2 X3 X6 : G) : (((X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ (X0 ◇ (X6 ◇ X0)))) ◇ X2))) ◇ X3) ◇ X1) = X3 := superpose eq569 eq353
  have eq575 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq569 eq375
  have eq578 (X0 X1 X2 X3 X6 : G) : (((X1 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X6 ◇ X0))))) ◇ X3) ◇ X1) = X3 := superpose eq569 eq570
  have eq579 (X1 X2 X3 X6 : G) : (((X1 ◇ (X3 ◇ (X2 ◇ X6))) ◇ X3) ◇ X1) = X3 := superpose eq569 eq578
  have eq580 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq467 eq575
  have eq585 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq580 eq467
  have eq591 (X1 X3 : G) : (X3 ◇ X1) = X3 := superpose eq585 eq579
  have eq606 (X0 X1 : G) : X0 = X1 := superpose eq585 eq591
  have eq608 (X0 : G) : sK0 ≠ X0 := superpose eq606 eq8
  subsumption eq608 eq606


@[equational_result]
theorem Equation38562_implies_Equation2 (G : Type*) [Magma G] (h : Equation38562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq10 eq13
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq14 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation38563_implies_Equation2 (G : Type*) [Magma G] (h : Equation38563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X2) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq11 eq14
  have eq17 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq16 eq11
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation38566_implies_Equation2 (G : Type*) [Magma G] (h : Equation38566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2))) ◇ X1) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ ((X2 ◇ X3) ◇ X2))) ◇ X1)) ◇ X2) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) = (X0 ◇ X2) := superpose eq10 eq7
  have eq41 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3) ◇ X4) = (((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3))) ◇ X1)) ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3))) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3))) ◇ X1))) := superpose eq9 eq19
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X2 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) ◇ X2) ◇ X3) := superpose eq10 eq19
  have eq49 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2) = X0 := superpose eq19 eq10
  have eq82 (X0 X2 X3 X4 : G) : (((X3 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X3) ◇ X4) = X2 := superpose eq49 eq41
  have eq83 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq82 eq46
  have eq84 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) = X3 := superpose eq83 eq10
  have eq117 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X2) = X3 := superpose eq83 eq84
  have eq139 (X0 X3 : G) : X0 = X3 := superpose eq117 eq117
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq139 eq8
  subsumption eq141 eq139


@[equational_result]
theorem Equation38567_implies_Equation2 (G : Type*) [Magma G] (h : Equation38567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation38570_implies_Equation2 (G : Type*) [Magma G] (h : Equation38570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq48 eq14


@[equational_result]
theorem Equation38571_implies_Equation2 (G : Type*) [Magma G] (h : Equation38571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38573_implies_Equation2 (G : Type*) [Magma G] (h : Equation38573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation38574_implies_Equation2 (G : Type*) [Magma G] (h : Equation38574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation38575_implies_Equation2 (G : Type*) [Magma G] (h : Equation38575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq30 eq18


@[equational_result]
theorem Equation38576_implies_Equation2 (G : Type*) [Magma G] (h : Equation38576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38578_implies_Equation2 (G : Type*) [Magma G] (h : Equation38578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ (X0 ◇ X5)) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ X5)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X4))) = X1 := superpose eq7 eq7
  have eq16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq16 eq9
  have eq44 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ ((((X4 ◇ X1) ◇ X5) ◇ ((X6 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0)) ◇ X7)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0))) = X1 := superpose eq7 eq11
  have eq47 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((((X2 ◇ X0) ◇ X3) ◇ ((X4 ◇ X1) ◇ X5)) ◇ X1) = (X0 ◇ ((((X6 ◇ ((((X2 ◇ X0) ◇ X3) ◇ ((X4 ◇ X1) ◇ X5)) ◇ X1)) ◇ X7) ◇ ((X8 ◇ (X1 ◇ X0)) ◇ X9)) ◇ (X1 ◇ X0))) := superpose eq11 eq11
  have eq72 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) = X3 := superpose eq11 eq11
  have eq78 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X1) ◇ X2) = ((((X3 ◇ (X0 ◇ X1)) ◇ X4) ◇ ((X5 ◇ X2) ◇ X6)) ◇ X2) := superpose eq11 eq9
  have eq85 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X0) ◇ X3) ◇ ((X4 ◇ X1) ◇ X5)) ◇ X1) = (X0 ◇ (((((X2 ◇ X0) ◇ X3) ◇ ((X4 ◇ X1) ◇ X5)) ◇ X1) ◇ (X1 ◇ X0))) := superpose eq78 eq47
  have eq89 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X0) ◇ X3) ◇ ((X4 ◇ X1) ◇ X5)) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq11 eq37
  have eq107 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ X1))) = X1 := superpose eq89 eq44
  have eq110 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq107
  have eq111 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X0) ◇ X3) ◇ ((X4 ◇ X1) ◇ X5)) ◇ X1) = X1 := superpose eq110 eq89
  have eq112 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq111 eq85
  have eq114 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X2 := superpose eq111 eq78
  have eq116 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) = X3 := superpose eq114 eq72
  have eq129 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X4))) = X1 := superpose eq114 eq12
  have eq138 (X0 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = X3 := superpose eq114 eq116
  have eq139 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq138 eq112
  have eq159 (X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X2) ◇ X4)) = X1 := superpose eq139 eq129
  have eq160 (X1 X2 X4 : G) : (X2 ◇ X4) = X1 := superpose eq139 eq159
  have eq161 (X0 X3 : G) : X0 = X3 := superpose eq160 eq160
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq161 eq8
  subsumption eq163 eq161


@[equational_result]
theorem Equation38579_implies_Equation2 (G : Type*) [Magma G] (h : Equation38579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq11 eq14
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq16 eq11
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation38580_implies_Equation2 (G : Type*) [Magma G] (h : Equation38580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq11 eq13
  have eq17 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq16 eq11
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation38581_implies_Equation2 (G : Type*) [Magma G] (h : Equation38581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X7 : G) : ((X0 ◇ X5) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (((X2 ◇ X0) ◇ X3) ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq11 eq13
  have eq17 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq16 eq11
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation38583_implies_Equation2 (G : Type*) [Magma G] (h : Equation38583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation38584_implies_Equation2 (G : Type*) [Magma G] (h : Equation38584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X5)) ◇ X1) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X4)) ◇ X2)) = X3 := superpose eq7 eq7
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq9 eq7
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq150 eq51


@[equational_result]
theorem Equation38585_implies_Equation2 (G : Type*) [Magma G] (h : Equation38585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ X4) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq62 eq17


@[equational_result]
theorem Equation38586_implies_Equation2 (G : Type*) [Magma G] (h : Equation38586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X6 : G) : (X0 ◇ X6) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation38588_implies_Equation2 (G : Type*) [Magma G] (h : Equation38588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4))) = X2 := superpose eq7 eq7
  have eq39 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq12 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq39
  have eq144 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq144 eq47


@[equational_result]
theorem Equation38589_implies_Equation2 (G : Type*) [Magma G] (h : Equation38589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation38590_implies_Equation2 (G : Type*) [Magma G] (h : Equation38590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38591_implies_Equation2 (G : Type*) [Magma G] (h : Equation38591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38593_implies_Equation2 (G : Type*) [Magma G] (h : Equation38593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation38594_implies_Equation2 (G : Type*) [Magma G] (h : Equation38594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38595_implies_Equation2 (G : Type*) [Magma G] (h : Equation38595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq44 eq15


@[equational_result]
theorem Equation38596_implies_Equation2 (G : Type*) [Magma G] (h : Equation38596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38598_implies_Equation2 (G : Type*) [Magma G] (h : Equation38598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : (((X1 ◇ X0) ◇ X6) ◇ X1) = X5 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation38599_implies_Equation2 (G : Type*) [Magma G] (h : Equation38599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38600_implies_Equation2 (G : Type*) [Magma G] (h : Equation38600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38601_implies_Equation2 (G : Type*) [Magma G] (h : Equation38601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X7 : G) : ((X0 ◇ X7) ◇ X7) = X5 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq34 eq16


@[equational_result]
theorem Equation38602_implies_Equation2 (G : Type*) [Magma G] (h : Equation38602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X8 : G) : (X0 ◇ X8) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38604_implies_Equation2 (G : Type*) [Magma G] (h : Equation38604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X3)) ◇ X3) ◇ X1) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq9
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X1 := superpose eq9 eq9
  have eq37 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq9 eq15
  have eq48 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq37 eq22
  have eq53 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq48 eq10
  have eq62 (X0 X1 : G) : X0 = X1 := superpose eq11 eq53
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq80 eq62


@[equational_result]
theorem Equation38606_implies_Equation2 (G : Type*) [Magma G] (h : Equation38606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq11 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation38608_implies_Equation2 (G : Type*) [Magma G] (h : Equation38608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq28 eq13


@[equational_result]
theorem Equation38610_implies_Equation2 (G : Type*) [Magma G] (h : Equation38610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ X4) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq50 eq18


@[equational_result]
theorem Equation38614_implies_Equation2 (G : Type*) [Magma G] (h : Equation38614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation38616_implies_Equation2 (G : Type*) [Magma G] (h : Equation38616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq50 eq18


@[equational_result]
theorem Equation38617_implies_Equation2 (G : Type*) [Magma G] (h : Equation38617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation38618_implies_Equation2 (G : Type*) [Magma G] (h : Equation38618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X4) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq37 eq16


@[equational_result]
theorem Equation38619_implies_Equation2 (G : Type*) [Magma G] (h : Equation38619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38621_implies_Equation2 (G : Type*) [Magma G] (h : Equation38621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X3) ◇ X1) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = X1 := superpose eq10 eq7
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X1 := superpose eq7 eq9
  have eq22 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = X1 := superpose eq10 eq9
  have eq27 (X1 X2 : G) : (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X1 := superpose eq20 eq11
  have eq28 (X1 : G) : (X1 ◇ (X1 ◇ X1)) = X1 := superpose eq22 eq16
  have eq29 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq28 eq9
  have eq38 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq27
  have eq54 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq29 eq29
  have eq69 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq54 eq7
  have eq71 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq54 eq38
  have eq76 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X0 := superpose eq71 eq69
  have eq91 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq71 eq76
  have eq92 (X0 X3 : G) : X0 = X3 := superpose eq91 eq91
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq94 eq92


@[equational_result]
theorem Equation38623_implies_Equation2 (G : Type*) [Magma G] (h : Equation38623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X1) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38625_implies_Equation2 (G : Type*) [Magma G] (h : Equation38625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38626_implies_Equation2 (G : Type*) [Magma G] (h : Equation38626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38627_implies_Equation2 (G : Type*) [Magma G] (h : Equation38627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38629_implies_Equation2 (G : Type*) [Magma G] (h : Equation38629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38630_implies_Equation2 (G : Type*) [Magma G] (h : Equation38630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38631_implies_Equation2 (G : Type*) [Magma G] (h : Equation38631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38633_implies_Equation2 (G : Type*) [Magma G] (h : Equation38633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38634_implies_Equation2 (G : Type*) [Magma G] (h : Equation38634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38635_implies_Equation2 (G : Type*) [Magma G] (h : Equation38635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38636_implies_Equation2 (G : Type*) [Magma G] (h : Equation38636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38640_implies_Equation2 (G : Type*) [Magma G] (h : Equation38640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X2) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38642_implies_Equation2 (G : Type*) [Magma G] (h : Equation38642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38643_implies_Equation2 (G : Type*) [Magma G] (h : Equation38643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38644_implies_Equation2 (G : Type*) [Magma G] (h : Equation38644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38646_implies_Equation2 (G : Type*) [Magma G] (h : Equation38646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38647_implies_Equation2 (G : Type*) [Magma G] (h : Equation38647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38648_implies_Equation2 (G : Type*) [Magma G] (h : Equation38648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38650_implies_Equation2 (G : Type*) [Magma G] (h : Equation38650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38651_implies_Equation2 (G : Type*) [Magma G] (h : Equation38651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38652_implies_Equation2 (G : Type*) [Magma G] (h : Equation38652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38653_implies_Equation2 (G : Type*) [Magma G] (h : Equation38653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38655_implies_Equation2 (G : Type*) [Magma G] (h : Equation38655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ (X0 ◇ X4)) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) ◇ X4) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) = X1 := superpose eq7 eq7
  have eq54 (X0 X1 : G) : X0 = X1 := superpose eq9 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq66 eq54


@[equational_result]
theorem Equation38656_implies_Equation2 (G : Type*) [Magma G] (h : Equation38656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) = X4 := superpose eq7 eq7
  have eq22 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq10 eq7
  have eq27 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq22 eq7
  have eq37 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq22 eq27
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation38657_implies_Equation2 (G : Type*) [Magma G] (h : Equation38657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq10 eq10
  have eq19 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X3) ◇ X3) = X0 := superpose eq12 eq7
  have eq23 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq19
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation38658_implies_Equation2 (G : Type*) [Magma G] (h : Equation38658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X1) ◇ X3) ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38660_implies_Equation2 (G : Type*) [Magma G] (h : Equation38660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38661_implies_Equation2 (G : Type*) [Magma G] (h : Equation38661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38662_implies_Equation2 (G : Type*) [Magma G] (h : Equation38662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38663_implies_Equation2 (G : Type*) [Magma G] (h : Equation38663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38665_implies_Equation2 (G : Type*) [Magma G] (h : Equation38665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38666_implies_Equation2 (G : Type*) [Magma G] (h : Equation38666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38667_implies_Equation2 (G : Type*) [Magma G] (h : Equation38667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38668_implies_Equation2 (G : Type*) [Magma G] (h : Equation38668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38670_implies_Equation2 (G : Type*) [Magma G] (h : Equation38670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38671_implies_Equation2 (G : Type*) [Magma G] (h : Equation38671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38672_implies_Equation2 (G : Type*) [Magma G] (h : Equation38672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38673_implies_Equation2 (G : Type*) [Magma G] (h : Equation38673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38675_implies_Equation2 (G : Type*) [Magma G] (h : Equation38675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38676_implies_Equation2 (G : Type*) [Magma G] (h : Equation38676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38677_implies_Equation2 (G : Type*) [Magma G] (h : Equation38677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38678_implies_Equation2 (G : Type*) [Magma G] (h : Equation38678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38679_implies_Equation2 (G : Type*) [Magma G] (h : Equation38679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38681_implies_Equation2 (G : Type*) [Magma G] (h : Equation38681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((((X1 ◇ X1) ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X3 ◇ X3) ◇ X1) ◇ ((X4 ◇ X4) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X0))) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X0))) = X1 := superpose eq7 eq9
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq7 eq9
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) := superpose eq10 eq10
  have eq24 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq27 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = ((X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ (((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1)) := superpose eq10 eq9
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) := superpose eq15 eq20
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0))) ◇ (((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1)) := superpose eq15 eq27
  have eq41 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq15 eq7
  have eq47 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X2) ◇ ((X3 ◇ X3) ◇ X1)) ◇ X1)) = X2 := superpose eq15 eq9
  have eq48 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = X2 := superpose eq15 eq7
  have eq72 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq9 eq48
  have eq81 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = ((X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) := superpose eq15 eq24
  have eq84 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq24
  have eq87 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = (((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) := superpose eq15 eq24
  have eq89 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq24 eq9
  have eq99 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := superpose eq24 eq7
  have eq107 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0)) = ((X1 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X0))) ◇ ((X3 ◇ X3) ◇ X1)) := superpose eq87 eq35
  have eq108 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq72 eq99
  have eq109 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq84 eq108
  have eq110 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq109 eq17
  have eq114 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq89 eq110
  have eq115 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq114 eq24
  have eq116 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = X0 := superpose eq72 eq115
  have eq117 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0)) := superpose eq116 eq31
  have eq120 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = X2 := superpose eq116 eq81
  have eq125 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := superpose eq47 eq117
  have eq129 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ X3) ◇ X1)) = X0 := superpose eq125 eq107
  have eq132 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq120 eq41
  have eq148 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq15 eq132
  have eq175 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X3 ◇ X3) ◇ X1) ◇ ((X4 ◇ X4) ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq148 eq11
  have eq183 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq148 eq129
  have eq188 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X3 ◇ X3) ◇ X1) ◇ X4) ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq148 eq175
  have eq189 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X3 ◇ X4) ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq148 eq188
  have eq196 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq183 eq189
  have eq199 (X0 X1 : G) : X0 = X1 := superpose eq15 eq196
  have eq212 (X0 : G) : sK0 ≠ X0 := superpose eq199 eq8
  subsumption eq212 eq199


@[equational_result]
theorem Equation38682_implies_Equation2 (G : Type*) [Magma G] (h : Equation38682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq9 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq9 eq12
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq20 eq13


@[equational_result]
theorem Equation38683_implies_Equation2 (G : Type*) [Magma G] (h : Equation38683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation38687_implies_Equation2 (G : Type*) [Magma G] (h : Equation38687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation38690_implies_Equation2 (G : Type*) [Magma G] (h : Equation38690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation38691_implies_Equation2 (G : Type*) [Magma G] (h : Equation38691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation38693_implies_Equation2 (G : Type*) [Magma G] (h : Equation38693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation38694_implies_Equation2 (G : Type*) [Magma G] (h : Equation38694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation38695_implies_Equation2 (G : Type*) [Magma G] (h : Equation38695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation38696_implies_Equation2 (G : Type*) [Magma G] (h : Equation38696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38700_implies_Equation2 (G : Type*) [Magma G] (h : Equation38700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X1) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38702_implies_Equation2 (G : Type*) [Magma G] (h : Equation38702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation38703_implies_Equation2 (G : Type*) [Magma G] (h : Equation38703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation38704_implies_Equation2 (G : Type*) [Magma G] (h : Equation38704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38706_implies_Equation2 (G : Type*) [Magma G] (h : Equation38706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation38707_implies_Equation2 (G : Type*) [Magma G] (h : Equation38707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation38708_implies_Equation2 (G : Type*) [Magma G] (h : Equation38708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38710_implies_Equation2 (G : Type*) [Magma G] (h : Equation38710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38711_implies_Equation2 (G : Type*) [Magma G] (h : Equation38711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38712_implies_Equation2 (G : Type*) [Magma G] (h : Equation38712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38713_implies_Equation2 (G : Type*) [Magma G] (h : Equation38713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38716_implies_Equation2 (G : Type*) [Magma G] (h : Equation38716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (((X2 ◇ X2) ◇ X2) ◇ X2) = X0 := superpose eq9 eq7
  have eq12 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq9 eq11
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38717_implies_Equation2 (G : Type*) [Magma G] (h : Equation38717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38719_implies_Equation2 (G : Type*) [Magma G] (h : Equation38719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38720_implies_Equation2 (G : Type*) [Magma G] (h : Equation38720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38721_implies_Equation2 (G : Type*) [Magma G] (h : Equation38721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38723_implies_Equation2 (G : Type*) [Magma G] (h : Equation38723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38724_implies_Equation2 (G : Type*) [Magma G] (h : Equation38724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38725_implies_Equation2 (G : Type*) [Magma G] (h : Equation38725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38727_implies_Equation2 (G : Type*) [Magma G] (h : Equation38727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38728_implies_Equation2 (G : Type*) [Magma G] (h : Equation38728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38729_implies_Equation2 (G : Type*) [Magma G] (h : Equation38729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38730_implies_Equation2 (G : Type*) [Magma G] (h : Equation38730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38732_implies_Equation2 (G : Type*) [Magma G] (h : Equation38732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) ◇ X4) ◇ X3) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) = X2 := superpose eq7 eq7
  have eq36 (X0 X1 : G) : X0 = X1 := superpose eq9 eq11
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq64 eq36


@[equational_result]
theorem Equation38733_implies_Equation2 (G : Type*) [Magma G] (h : Equation38733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ X2) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq10 eq12
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38734_implies_Equation2 (G : Type*) [Magma G] (h : Equation38734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ X3) ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38735_implies_Equation2 (G : Type*) [Magma G] (h : Equation38735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (((X2 ◇ X2) ◇ X3) ◇ X4) = X0 := superpose eq11 eq7
  have eq15 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq11 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38737_implies_Equation2 (G : Type*) [Magma G] (h : Equation38737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38738_implies_Equation2 (G : Type*) [Magma G] (h : Equation38738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38739_implies_Equation2 (G : Type*) [Magma G] (h : Equation38739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38740_implies_Equation2 (G : Type*) [Magma G] (h : Equation38740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38742_implies_Equation2 (G : Type*) [Magma G] (h : Equation38742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38743_implies_Equation2 (G : Type*) [Magma G] (h : Equation38743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38744_implies_Equation2 (G : Type*) [Magma G] (h : Equation38744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38745_implies_Equation2 (G : Type*) [Magma G] (h : Equation38745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38747_implies_Equation2 (G : Type*) [Magma G] (h : Equation38747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38748_implies_Equation2 (G : Type*) [Magma G] (h : Equation38748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38749_implies_Equation2 (G : Type*) [Magma G] (h : Equation38749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation38750_implies_Equation2 (G : Type*) [Magma G] (h : Equation38750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38752_implies_Equation2 (G : Type*) [Magma G] (h : Equation38752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38753_implies_Equation2 (G : Type*) [Magma G] (h : Equation38753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38754_implies_Equation2 (G : Type*) [Magma G] (h : Equation38754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38755_implies_Equation2 (G : Type*) [Magma G] (h : Equation38755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38756_implies_Equation2 (G : Type*) [Magma G] (h : Equation38756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38758_implies_Equation2 (G : Type*) [Magma G] (h : Equation38758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (((X1 ◇ (X0 ◇ X5)) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq26 (X0 X1 X5 : G) : ((X0 ◇ X5) ◇ X1) = X5 := superpose eq16 eq9
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq26 eq10
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation38759_implies_Equation2 (G : Type*) [Magma G] (h : Equation38759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X3) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ X2) = X4 := superpose eq7 eq7
  have eq15 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X3 := superpose eq11 eq10
  have eq16 (X0 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X3 := superpose eq11 eq15
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq11 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq28 eq21


@[equational_result]
theorem Equation38760_implies_Equation2 (G : Type*) [Magma G] (h : Equation38760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq11 eq10
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation38761_implies_Equation2 (G : Type*) [Magma G] (h : Equation38761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : (((X1 ◇ X0) ◇ X5) ◇ X6) = X5 := superpose eq7 eq7
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq15 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation38763_implies_Equation2 (G : Type*) [Magma G] (h : Equation38763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation38764_implies_Equation2 (G : Type*) [Magma G] (h : Equation38764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X5)) ◇ X1) ◇ ((X2 ◇ ((X3 ◇ X4) ◇ X0)) ◇ X2)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X3 := superpose eq7 eq7
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq10 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq51 eq40


@[equational_result]
theorem Equation38765_implies_Equation2 (G : Type*) [Magma G] (h : Equation38765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation38766_implies_Equation2 (G : Type*) [Magma G] (h : Equation38766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation38768_implies_Equation2 (G : Type*) [Magma G] (h : Equation38768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0))) = X3 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq12
  have eq59 (X0 X5 : G) : X0 = X5 := superpose eq12 eq33
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq149 eq59


@[equational_result]
theorem Equation38769_implies_Equation2 (G : Type*) [Magma G] (h : Equation38769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X2) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation38770_implies_Equation2 (G : Type*) [Magma G] (h : Equation38770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38771_implies_Equation2 (G : Type*) [Magma G] (h : Equation38771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X6) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38773_implies_Equation2 (G : Type*) [Magma G] (h : Equation38773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation38774_implies_Equation2 (G : Type*) [Magma G] (h : Equation38774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38775_implies_Equation2 (G : Type*) [Magma G] (h : Equation38775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq44 eq15


@[equational_result]
theorem Equation38776_implies_Equation2 (G : Type*) [Magma G] (h : Equation38776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38778_implies_Equation2 (G : Type*) [Magma G] (h : Equation38778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : (((X1 ◇ X0) ◇ X6) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation38779_implies_Equation2 (G : Type*) [Magma G] (h : Equation38779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38780_implies_Equation2 (G : Type*) [Magma G] (h : Equation38780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X6 : G) : (X0 ◇ X5) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38781_implies_Equation2 (G : Type*) [Magma G] (h : Equation38781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X7) ◇ X7) = X6 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq34 eq16


@[equational_result]
theorem Equation38782_implies_Equation2 (G : Type*) [Magma G] (h : Equation38782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X8 : G) : (X0 ◇ X8) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation38784_implies_Equation2 (G : Type*) [Magma G] (h : Equation38784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X1) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X1) = X0 := superpose eq15 eq7
  have eq23 (X0 X1 X5 : G) : ((X0 ◇ X5) ◇ X1) = X5 := superpose eq15 eq9
  have eq24 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq23 eq22
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation38785_implies_Equation2 (G : Type*) [Magma G] (h : Equation38785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) ◇ X5) ◇ (X2 ◇ X0)) = X5 := superpose eq7 eq10
  have eq33 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) := superpose eq11 eq11
  have eq34 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq10 eq11
  have eq47 (X3 X4 : G) : (X3 ◇ X4) = X3 := superpose eq34 eq33
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) ◇ (X2 ◇ X0)) = X5 := superpose eq47 eq18
  have eq72 (X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) ◇ X2) = X5 := superpose eq47 eq49
  have eq73 (X1 X2 X3 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2) = X5 := superpose eq47 eq72
  have eq74 (X1 X2 X5 : G) : (X1 ◇ X2) = X5 := superpose eq47 eq73
  have eq75 (X0 X3 : G) : X0 = X3 := superpose eq74 eq74
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq80 eq75


@[equational_result]
theorem Equation38786_implies_Equation2 (G : Type*) [Magma G] (h : Equation38786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq7 eq10
  have eq19 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X1) ◇ X3) = X0 := superpose eq12 eq7
  have eq23 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq12 eq19
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation38787_implies_Equation2 (G : Type*) [Magma G] (h : Equation38787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X1) ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38789_implies_Equation2 (G : Type*) [Magma G] (h : Equation38789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38790_implies_Equation2 (G : Type*) [Magma G] (h : Equation38790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38791_implies_Equation2 (G : Type*) [Magma G] (h : Equation38791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38792_implies_Equation2 (G : Type*) [Magma G] (h : Equation38792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38794_implies_Equation2 (G : Type*) [Magma G] (h : Equation38794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38795_implies_Equation2 (G : Type*) [Magma G] (h : Equation38795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38796_implies_Equation2 (G : Type*) [Magma G] (h : Equation38796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38797_implies_Equation2 (G : Type*) [Magma G] (h : Equation38797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38799_implies_Equation2 (G : Type*) [Magma G] (h : Equation38799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38800_implies_Equation2 (G : Type*) [Magma G] (h : Equation38800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38801_implies_Equation2 (G : Type*) [Magma G] (h : Equation38801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38802_implies_Equation2 (G : Type*) [Magma G] (h : Equation38802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38804_implies_Equation2 (G : Type*) [Magma G] (h : Equation38804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38805_implies_Equation2 (G : Type*) [Magma G] (h : Equation38805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38806_implies_Equation2 (G : Type*) [Magma G] (h : Equation38806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38807_implies_Equation2 (G : Type*) [Magma G] (h : Equation38807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38808_implies_Equation2 (G : Type*) [Magma G] (h : Equation38808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38810_implies_Equation2 (G : Type*) [Magma G] (h : Equation38810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3))) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X1)) = X0 := superpose eq7 eq11
  have eq28 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq20 eq7
  have eq35 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq28 eq20
  have eq38 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq35 eq28
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq38 eq38
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq41 eq39


@[equational_result]
theorem Equation38811_implies_Equation2 (G : Type*) [Magma G] (h : Equation38811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X2) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq10 eq13
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38812_implies_Equation2 (G : Type*) [Magma G] (h : Equation38812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq10 eq13
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38813_implies_Equation2 (G : Type*) [Magma G] (h : Equation38813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X2) ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38815_implies_Equation2 (G : Type*) [Magma G] (h : Equation38815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38816_implies_Equation2 (G : Type*) [Magma G] (h : Equation38816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38817_implies_Equation2 (G : Type*) [Magma G] (h : Equation38817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38818_implies_Equation2 (G : Type*) [Magma G] (h : Equation38818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38820_implies_Equation2 (G : Type*) [Magma G] (h : Equation38820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38821_implies_Equation2 (G : Type*) [Magma G] (h : Equation38821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38822_implies_Equation2 (G : Type*) [Magma G] (h : Equation38822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38823_implies_Equation2 (G : Type*) [Magma G] (h : Equation38823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38825_implies_Equation2 (G : Type*) [Magma G] (h : Equation38825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38826_implies_Equation2 (G : Type*) [Magma G] (h : Equation38826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38827_implies_Equation2 (G : Type*) [Magma G] (h : Equation38827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation38828_implies_Equation2 (G : Type*) [Magma G] (h : Equation38828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38830_implies_Equation2 (G : Type*) [Magma G] (h : Equation38830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38831_implies_Equation2 (G : Type*) [Magma G] (h : Equation38831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38832_implies_Equation2 (G : Type*) [Magma G] (h : Equation38832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38833_implies_Equation2 (G : Type*) [Magma G] (h : Equation38833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38834_implies_Equation2 (G : Type*) [Magma G] (h : Equation38834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38836_implies_Equation2 (G : Type*) [Magma G] (h : Equation38836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X1) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq25 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X1) = X0 := superpose eq16 eq7
  have eq26 (X0 X1 X5 : G) : ((X0 ◇ X5) ◇ X1) = X5 := superpose eq16 eq9
  have eq27 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq26 eq25
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation38837_implies_Equation2 (G : Type*) [Magma G] (h : Equation38837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38838_implies_Equation2 (G : Type*) [Magma G] (h : Equation38838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq11 eq13
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38839_implies_Equation2 (G : Type*) [Magma G] (h : Equation38839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X3) ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38841_implies_Equation2 (G : Type*) [Magma G] (h : Equation38841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38842_implies_Equation2 (G : Type*) [Magma G] (h : Equation38842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38843_implies_Equation2 (G : Type*) [Magma G] (h : Equation38843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38844_implies_Equation2 (G : Type*) [Magma G] (h : Equation38844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38846_implies_Equation2 (G : Type*) [Magma G] (h : Equation38846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38847_implies_Equation2 (G : Type*) [Magma G] (h : Equation38847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38848_implies_Equation2 (G : Type*) [Magma G] (h : Equation38848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38849_implies_Equation2 (G : Type*) [Magma G] (h : Equation38849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38851_implies_Equation2 (G : Type*) [Magma G] (h : Equation38851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38852_implies_Equation2 (G : Type*) [Magma G] (h : Equation38852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38853_implies_Equation2 (G : Type*) [Magma G] (h : Equation38853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38854_implies_Equation2 (G : Type*) [Magma G] (h : Equation38854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38856_implies_Equation2 (G : Type*) [Magma G] (h : Equation38856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38857_implies_Equation2 (G : Type*) [Magma G] (h : Equation38857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38858_implies_Equation2 (G : Type*) [Magma G] (h : Equation38858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38859_implies_Equation2 (G : Type*) [Magma G] (h : Equation38859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38860_implies_Equation2 (G : Type*) [Magma G] (h : Equation38860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38862_implies_Equation2 (G : Type*) [Magma G] (h : Equation38862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X6 X7 : G) : (((X1 ◇ (X0 ◇ X6)) ◇ X7) ◇ X1) = X7 := superpose eq7 eq7
  have eq10 (X0 X1 X6 : G) : (((X1 ◇ X0) ◇ X6) ◇ X1) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq26 (X0 X1 X7 : G) : ((X0 ◇ X7) ◇ X1) = X7 := superpose eq16 eq9
  have eq27 (X0 X1 X6 : G) : (X0 ◇ X1) = X6 := superpose eq26 eq10
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation38863_implies_Equation2 (G : Type*) [Magma G] (h : Equation38863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X7 : G) : ((X0 ◇ X7) ◇ X2) = X7 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq11 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38864_implies_Equation2 (G : Type*) [Magma G] (h : Equation38864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X7 : G) : ((X0 ◇ X7) ◇ X4) = X7 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq11 eq13
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38865_implies_Equation2 (G : Type*) [Magma G] (h : Equation38865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 : G) : ((X0 ◇ X7) ◇ X6) = X7 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X4) ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38866_implies_Equation2 (G : Type*) [Magma G] (h : Equation38866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X0) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X8 X9 : G) : ((X0 ◇ X8) ◇ X9) = X8 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X4) ◇ X5) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 X5 : G) : (X3 ◇ X5) = X0 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38868_implies_Equation2 (G : Type*) [Magma G] (h : Equation38868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38869_implies_Equation2 (G : Type*) [Magma G] (h : Equation38869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38870_implies_Equation2 (G : Type*) [Magma G] (h : Equation38870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38871_implies_Equation2 (G : Type*) [Magma G] (h : Equation38871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38872_implies_Equation2 (G : Type*) [Magma G] (h : Equation38872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38874_implies_Equation2 (G : Type*) [Magma G] (h : Equation38874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38875_implies_Equation2 (G : Type*) [Magma G] (h : Equation38875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38876_implies_Equation2 (G : Type*) [Magma G] (h : Equation38876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38877_implies_Equation2 (G : Type*) [Magma G] (h : Equation38877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38878_implies_Equation2 (G : Type*) [Magma G] (h : Equation38878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X2) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38880_implies_Equation2 (G : Type*) [Magma G] (h : Equation38880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38881_implies_Equation2 (G : Type*) [Magma G] (h : Equation38881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38882_implies_Equation2 (G : Type*) [Magma G] (h : Equation38882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38883_implies_Equation2 (G : Type*) [Magma G] (h : Equation38883 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38884_implies_Equation2 (G : Type*) [Magma G] (h : Equation38884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38886_implies_Equation2 (G : Type*) [Magma G] (h : Equation38886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38887_implies_Equation2 (G : Type*) [Magma G] (h : Equation38887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38888_implies_Equation2 (G : Type*) [Magma G] (h : Equation38888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38889_implies_Equation2 (G : Type*) [Magma G] (h : Equation38889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation38890_implies_Equation2 (G : Type*) [Magma G] (h : Equation38890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38892_implies_Equation2 (G : Type*) [Magma G] (h : Equation38892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38893_implies_Equation2 (G : Type*) [Magma G] (h : Equation38893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38894_implies_Equation2 (G : Type*) [Magma G] (h : Equation38894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38895_implies_Equation2 (G : Type*) [Magma G] (h : Equation38895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38896_implies_Equation2 (G : Type*) [Magma G] (h : Equation38896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation38897_implies_Equation2 (G : Type*) [Magma G] (h : Equation38897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


